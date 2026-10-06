module

public import FalconerPacking.CircularReciprocal
public import FalconerPacking.PlanarStripPackets
public import FalconerPacking.RadialProjectionTransversality

/-!
# Spatial packet amplitudes restricted to circles

The bounds concern the actual compact source cutoff and actual strip weights. Their constants
are independent of the pin, strip index, width, and unit-bounded strip normal.
-/

@[expose] public section

open Set Function Finset MeasureTheory
open scoped ContDiff RealInnerProductSpace

namespace FalconerPacking

/-- Every derivative of the unit-circle parametrization is a quarter turn. -/
theorem iteratedDeriv_angularDirection (n : ℕ) (θ : ℝ) :
    iteratedDeriv n angularDirection θ = angularDirection (θ + n * (Real.pi / 2)) := by
  induction n generalizing θ with
  | zero => simp only [iteratedDeriv_zero, Nat.cast_zero, zero_mul, add_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv n angularDirection =
      (fun t ↦ angularDirection (t + n * (Real.pi / 2))) from funext ih]
    have h := (hasDerivAt_angularDirection (θ + n * (Real.pi / 2))).scomp θ
      ((hasDerivAt_id θ).add_const (n * (Real.pi / 2)))
    rw [show deriv (fun t ↦ angularDirection (t + n * (Real.pi / 2))) θ =
      angularDirection (θ + n * (Real.pi / 2) + Real.pi / 2) by
        simpa only [Function.comp_def, id_eq, one_smul,
          angularTangent_eq_direction] using h.deriv]
    congr 1
    push_cast
    ring

/-- Positive-order derivatives of a circle centered at any pin have exactly norm `|r|`. -/
theorem norm_iteratedDeriv_pinnedCircle (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    {n : ℕ} (hn : 0 < n) (θ : ℝ) :
    ‖iteratedDeriv n (fun t ↦ y - r • angularDirection t) θ‖ = |r| := by
  rw [iteratedDeriv_const_sub hn, iteratedDeriv_neg,
    iteratedDeriv_fun_const_smul_field, iteratedDeriv_angularDirection,
    norm_neg, norm_smul, norm_angularDirection, mul_one, Real.norm_eq_abs]

/-- The actual scalar spatial packet evaluated along a pinned circle. -/
noncomputable def circularPacketAmplitude
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (w : ℝ)
    (e y : EuclideanSpace ℝ (Fin 2)) (j : ℤ) (r : ℝ) (θ : ℝ) : ℝ :=
  smoothStripPacket χ w e j (y - r • angularDirection θ)

theorem contDiff_circularPacketAmplitude
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (w : ℝ)
    (e y : EuclideanSpace ℝ (Fin 2)) (j : ℤ) (r : ℝ) :
    ContDiff ℝ ∞ (circularPacketAmplitude χ w e y j r) :=
  (contDiff_smoothStripPacket χ w e j).comp
    (contDiff_const.sub (ContDiff.const_smul r contDiff_angularDirection))

/-- A uniform spatial derivative constant for all orders through `N`. -/
theorem exists_uniform_smoothStripPacket_derivative_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, 0 < w → w ≤ 1 →
      ∀ e : EuclideanSpace ℝ (Fin 2), ‖e‖ ≤ 1 → ∀ (j : ℤ) (n : ℕ), n ≤ N →
        ∀ x, ‖iteratedFDeriv ℝ n (smoothStripPacket χ w e j) x‖ ≤ C * w⁻¹ ^ n := by
  choose D hD hbound using exists_smoothStripPacket_derivative_bound_of_le_one χ
  have hsum : 0 ≤ ∑ n ∈ range (N + 1), D n := sum_nonneg (fun n _ ↦ hD n)
  refine ⟨1 + ∑ n ∈ range (N + 1), D n, by linarith, ?_⟩
  intro w hw hw₁ e he j n hn x
  apply (hbound n w hw hw₁ e he j x).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have h := single_le_sum (fun i (_ : i ∈ range (N + 1)) ↦ hD i)
    (show n ∈ range (N + 1) from Finset.mem_range.mpr (by omega))
  linarith

/-- Angular differentiation of the packet costs only one inverse width per derivative. -/
theorem exists_circularPacketAmplitude_derivative_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (N : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, 0 < w → w ≤ 1 →
      ∀ e y : EuclideanSpace ℝ (Fin 2), ‖e‖ ≤ 1 → ∀ (j : ℤ) (r : ℝ), |r| ≤ R →
        ∀ k ≤ N, ∀ θ, ‖iteratedDeriv k (circularPacketAmplitude χ w e y j r) θ‖ ≤
          C * w⁻¹ ^ k := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_smoothStripPacket_derivative_bound χ N
  refine ⟨circularReciprocalPartitionBound N * B * (max 1 R) ^ N, ?_, ?_⟩
  · have := circularReciprocalPartitionBound_pos N
    positivity
  intro w hw hw₁ e y he j r hr k hk θ
  have hwInv : 1 ≤ w⁻¹ := (one_le_inv₀ hw).mpr hw₁
  have hR : 1 ≤ max 1 R := le_max_left _ _
  change ‖iteratedDeriv k (smoothStripPacket χ w e j ∘
    (fun t ↦ y - r • angularDirection t)) θ‖ ≤ _
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition
    (contDiff_smoothStripPacket χ w e j).contDiffAt
    (show ContDiff ℝ ∞ (fun t ↦ y - r • angularDirection t) from
      contDiff_const.sub (ContDiff.const_smul r contDiff_angularDirection)).contDiffAt
    (by exact_mod_cast le_top)]
  calc
    _ ≤ ∑ c : OrderedFinpartition k,
        ‖iteratedFDeriv ℝ c.length (smoothStripPacket χ w e j)
          (y - r • angularDirection θ)
          (fun i ↦ iteratedDeriv (c.partSize i) (fun t ↦ y - r • angularDirection t) θ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _c : OrderedFinpartition k, B * w⁻¹ ^ k * (max 1 R) ^ N := by
      apply sum_le_sum
      intro c _
      have hout : ‖iteratedFDeriv ℝ c.length (smoothStripPacket χ w e j)
          (y - r • angularDirection θ)‖ ≤ B * w⁻¹ ^ k :=
        (hbound w hw hw₁ e he j c.length (c.length_le.trans hk) _).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hwInv c.length_le) hB.le)
      have hprod : (∏ i : Fin c.length,
          ‖iteratedDeriv (c.partSize i) (fun t ↦ y - r • angularDirection t) θ‖) ≤
          (max 1 R) ^ N := by
        simp only [norm_iteratedDeriv_pinnedCircle y r (c.partSize_pos _),
          prod_const, card_univ, Fintype.card_fin]
        exact (pow_le_pow_left₀ (abs_nonneg r) (hr.trans (le_max_right _ _)) _).trans
          (pow_le_pow_right₀ hR (c.length_le.trans hk))
      exact (ContinuousMultilinearMap.le_opNorm _ _).trans
        (mul_le_mul hout hprod (by positivity) (by positivity))
    _ = (Fintype.card (OrderedFinpartition k) : ℝ) *
        (B * w⁻¹ ^ k * (max 1 R) ^ N) := by simp
    _ ≤ circularReciprocalPartitionBound N * (B * w⁻¹ ^ k * (max 1 R) ^ N) :=
      mul_le_mul_of_nonneg_right
        (card_orderedFinpartition_le_circularReciprocalPartitionBound hk) (by positivity)
    _ = _ := by ring

/-- The closed angular support still lies in the closed physical strip. -/
theorem tsupport_circularPacketAmplitude_subset
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) {w : ℝ} (hw : 0 < w)
    (e y : EuclideanSpace ℝ (Fin 2)) (j : ℤ) (r : ℝ) :
    tsupport (circularPacketAmplitude χ w e y j r) ⊆
      {θ | |⟪e, y - r • angularDirection θ⟫ - w * j| ≤ w} := by
  apply closure_minimal
  · intro θ hθ
    exact (show |⟪e, y - r • angularDirection θ⟫ - w * j| < w from
      (support_smoothStripPacket χ hw e j hθ).2).le
  · exact isClosed_le (by fun_prop) continuous_const

/-- Rotation exchanges the strip-normal component with the phase's tangential component. -/
theorem inner_direction_tangent_eq_neg_normal (α θ : ℝ) :
    ⟪angularDirection α, angularTangent θ⟫ =
      -⟪angularDirection (α + Real.pi / 2), angularDirection θ⟫ := by
  rw [angularTangent_eq_direction, inner_angularDirection, inner_angularDirection]
  simp only [Real.cos_sub, Real.cos_add, Real.sin_add, Real.cos_pi_div_two,
    Real.sin_pi_div_two, mul_zero, mul_one, zero_sub, zero_add]
  ring

/-- A pin outside a strip forces a tangential phase component at every supported circle point. -/
theorem strip_separation_le_tangential_phase {y : EuclideanSpace ℝ (Fin 2)}
    {w r α θ : ℝ} {j : ℤ}
    (hstrip : |⟪angularDirection (α + Real.pi / 2), y - r • angularDirection θ⟫ - w * j| ≤ w) :
    |⟪angularDirection (α + Real.pi / 2), y⟫ - w * j| - w ≤
      |r * ⟪angularDirection α, angularTangent θ⟫| := by
  rw [inner_sub_right, inner_smul_right] at hstrip
  have hab := abs_sub_abs_le_abs_sub
    (⟪angularDirection (α + Real.pi / 2), y⟫ - w * j)
    (r * ⟪angularDirection (α + Real.pi / 2), angularDirection θ⟫)
  have he : ⟪angularDirection (α + Real.pi / 2), y⟫ - w * j -
      r * ⟪angularDirection (α + Real.pi / 2), angularDirection θ⟫ =
      ⟪angularDirection (α + Real.pi / 2), y⟫ -
        r * ⟪angularDirection (α + Real.pi / 2), angularDirection θ⟫ - w * j := by ring
  rw [he] at hab
  rw [inner_direction_tangent_eq_neg_normal, mul_neg, abs_neg]
  linarith

/-- Changing the phase direction costs at most radius times directional error. -/
theorem abs_tangential_phase_sub_le (v v₀ : EuclideanSpace ℝ (Fin 2)) (r θ : ℝ) :
    |r * ⟪v, angularTangent θ⟫ - r * ⟪v₀, angularTangent θ⟫| ≤ |r| * ‖v - v₀‖ := by
  rw [← mul_sub, ← inner_sub_left, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [norm_angularTangent, mul_one] using
      abs_real_inner_le_norm (v - v₀) (angularTangent θ)) (abs_nonneg r)

/-- Remote pins give nonstationarity for nearby cap directions on the closed packet support. -/
theorem le_abs_deriv_circularPhase_of_packet_support
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ)
    {w r α θ γ ε : ℝ} {j : ℤ} {v y : EuclideanSpace ℝ (Fin 2)} (hw : 0 < w)
    (hnear : ‖v - angularDirection α‖ ≤ ε)
    (hremote : γ + w + |r| * ε ≤ |⟪angularDirection (α + Real.pi / 2), y⟫ - w * j|)
    (hθ : θ ∈ tsupport
      (circularPacketAmplitude χ w (angularDirection (α + Real.pi / 2)) y j r)) :
    γ ≤ |deriv (circularPhase (r • v)) θ| := by
  have hstrip := tsupport_circularPacketAmplitude_subset χ hw
    (angularDirection (α + Real.pi / 2)) y j r hθ
  have hbase := strip_separation_le_tangential_phase hstrip
  have herr := (abs_tangential_phase_sub_le v (angularDirection α) r θ).trans
    (mul_le_mul_of_nonneg_left hnear (abs_nonneg r))
  have hab := abs_sub_abs_le_abs_sub (r * ⟪angularDirection α, angularTangent θ⟫)
    (r * ⟪v, angularTangent θ⟫)
  rw [abs_sub_comm] at hab
  rw [deriv_circularPhase, circularPhase, real_inner_smul_left,
    ← angularTangent_eq_direction]
  linarith

/-- An actual compact angular cutoff applied to the actual circle-restricted packet. -/
noncomputable def circularPacketArcAmplitude
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (w : ℝ)
    (e y : EuclideanSpace ℝ (Fin 2)) (j ℓ : ℤ) (r : ℝ) (θ : ℝ) : ℂ :=
  (smoothStripWeight w ℓ θ : ℂ) * (circularPacketAmplitude χ w e y j r θ : ℂ)

theorem contDiff_circularPacketArcAmplitude
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (w : ℝ)
    (e y : EuclideanSpace ℝ (Fin 2)) (j ℓ : ℤ) (r : ℝ) :
    ContDiff ℝ ∞ (circularPacketArcAmplitude χ w e y j ℓ r) :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_smoothStripWeight w ℓ)).mul
    (Complex.ofRealCLM.contDiff.comp (contDiff_circularPacketAmplitude χ w e y j r))

theorem tsupport_circularPacketArcAmplitude_subset_interval
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) {w : ℝ} (hw : 0 < w)
    (e y : EuclideanSpace ℝ (Fin 2)) (j ℓ : ℤ) (r : ℝ) :
    tsupport (circularPacketArcAmplitude χ w e y j ℓ r) ⊆
      Icc (w * ℓ - w) (w * ℓ + w) := by
  apply closure_minimal _ isClosed_Icc
  intro θ hθ
  have hne : smoothStripWeight w ℓ θ ≠ 0 := by
    intro hz
    exact hθ (by simp [circularPacketArcAmplitude, hz])
  have hs := abs_lt.mp (smoothStripWeight_support hw ℓ hne)
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem hasCompactSupport_circularPacketArcAmplitude
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) {w : ℝ} (hw : 0 < w)
    (e y : EuclideanSpace ℝ (Fin 2)) (j ℓ : ℤ) (r : ℝ) :
    HasCompactSupport (circularPacketArcAmplitude χ w e y j ℓ r) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((subset_tsupport _).trans
      (tsupport_circularPacketArcAmplitude_subset_interval χ hw e y j ℓ r))

theorem tsupport_circularPacketArcAmplitude_subset_packet
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (w : ℝ)
    (e y : EuclideanSpace ℝ (Fin 2)) (j ℓ : ℤ) (r : ℝ) :
    tsupport (circularPacketArcAmplitude χ w e y j ℓ r) ⊆
      tsupport (circularPacketAmplitude χ w e y j r) :=
  tsupport_mul_subset_right.trans (tsupport_comp_subset Complex.ofReal_zero _)

/-- Adding the actual angular cutoff preserves the same inverse-width derivative scale. -/
theorem exists_circularPacketArcAmplitude_derivative_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (N : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, 0 < w → w ≤ 1 →
      ∀ e y : EuclideanSpace ℝ (Fin 2), ‖e‖ ≤ 1 → ∀ (j ℓ : ℤ) (r : ℝ), |r| ≤ R →
        ∀ k ≤ N, ∀ θ, ‖iteratedDeriv k (circularPacketArcAmplitude χ w e y j ℓ r) θ‖ ≤
          C * w⁻¹ ^ k := by
  obtain ⟨B, hB, hb⟩ := exists_circularPacketAmplitude_derivative_bound χ N R
  choose D hD hd using exists_smoothStripWeight_derivative_bound
  let E := 1 + ∑ i ∈ range (N + 1), D i
  have hE : 0 < E := by
    have := sum_nonneg (fun i (_ : i ∈ range (N + 1)) ↦ hD i)
    dsimp only [E]
    linarith
  have hDE : ∀ i ≤ N, D i ≤ E := by
    intro i hi
    have := single_le_sum (fun l (_ : l ∈ range (N + 1)) ↦ hD l)
      (show i ∈ range (N + 1) from Finset.mem_range.mpr (by omega))
    dsimp only [E]
    linarith
  refine ⟨2 ^ N * E * B, by positivity, ?_⟩
  intro w hw hw₁ e y he j ℓ r hr k hk θ
  have h := norm_iteratedDeriv_mul_le
    (Complex.ofRealCLM.contDiff.comp (contDiff_smoothStripWeight w ℓ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_circularPacketAmplitude χ w e y j r))
    hE.le (show 0 ≤ w⁻¹ by positivity) k θ
    (fun i hi ↦ by
      change ‖iteratedDeriv i (fun t ↦ (smoothStripWeight w ℓ t : ℂ)) θ‖ ≤ _
      rw [iteratedDeriv_ofReal (contDiff_smoothStripWeight w ℓ), Complex.norm_real]
      exact (hd i w hw ℓ θ).trans
        (mul_le_mul_of_nonneg_right (hDE i (hi.trans hk)) (by positivity)))
    (fun i hi ↦ by
      change ‖iteratedDeriv i (fun t ↦ (circularPacketAmplitude χ w e y j r t : ℂ)) θ‖ ≤ _
      rw [iteratedDeriv_ofReal (contDiff_circularPacketAmplitude χ w e y j r), Complex.norm_real]
      exact hb w hw hw₁ e y he j r hr i (hi.trans hk) θ)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hE.le) hB.le)
    (by positivity))

/-- A remote-pin oscillatory bound for actual packets and actual compact angular cutoffs.
The constant depends only on the order, source cutoff, radius bound, and phase-vector bound. -/
theorem exists_remote_circularPacketArc_integral_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (N : ℕ) (R S : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w γ : ℝ), 0 < w → w ≤ γ → γ ≤ 1 →
      ∀ (v y : EuclideanSpace ℝ (Fin 2)) (α ε r : ℝ) (j ℓ : ℤ),
        |r| ≤ R → ‖r • v‖ ≤ S → ‖v - angularDirection α‖ ≤ ε →
        γ + w + |r| * ε ≤ |⟪angularDirection (α + Real.pi / 2), y⟫ - w * j| →
        ∀ t : ℝ, t ≠ 0 →
          ‖∫ θ, oscillatoryPhase (circularPhase (r • v)) t θ *
            circularPacketArcAmplitude χ w (angularDirection (α + Real.pi / 2)) y j ℓ r θ‖ ≤
              C * w * (|t| * w * γ)⁻¹ ^ N := by
  obtain ⟨B, hB, hbound⟩ := exists_circularPacketArcAmplitude_derivative_bound χ N R
  let Q := circularReciprocalDerivativeBound N S
  have hQ : 0 < Q := circularReciprocalDerivativeBound_pos N S
  refine ⟨2 * (2 ^ N * Q) ^ N * B, by positivity, ?_⟩
  intro w γ hw hwγ hγ₁ v y α ε r j ℓ hr hrv hnear hremote t ht
  have hγ : 0 < γ := hw.trans_le hwγ
  have hqφ : ∀ θ ∈ tsupport
      (circularPacketArcAmplitude χ w (angularDirection (α + Real.pi / 2)) y j ℓ r),
      circularReciprocal γ (r • v) θ * deriv (circularPhase (r • v)) θ = 1 := by
    intro θ hθ
    apply circularReciprocal_mul_deriv_eq_one (r • v) hγ
    exact le_abs_deriv_circularPhase_of_packet_support χ hw hnear hremote
      (tsupport_circularPacketArcAmplitude_subset_packet χ w _ y j ℓ r hθ)
  have h := norm_integral_oscillatoryPhase_mul_scale_le
    (contDiff_circularPhase (r • v)) (contDiff_circularReciprocal γ (r • v))
    (contDiff_circularPacketArcAmplitude χ w _ y j ℓ r)
    (hasCompactSupport_circularPacketArcAmplitude χ hw _ y j ℓ r) hqφ hQ.le hB.le hw hγ
    (tsupport_circularPacketArcAmplitude_subset_interval χ hw _ y j ℓ r) N
    (fun k hk θ ↦ norm_iteratedDeriv_circularReciprocal_scale_le (r • v) hw hwγ hγ₁ hrv hk θ)
    (hbound w hw (hwγ.trans hγ₁) _ y (by simp) j ℓ r hr) ht
  have hlen : max (w * ℓ + w - (w * ℓ - w)) 0 = 2 * w := by
    rw [show w * ℓ + w - (w * ℓ - w) = 2 * w by ring, max_eq_left (by positivity)]
  rw [hlen] at h
  convert h using 1
  ring

end FalconerPacking
