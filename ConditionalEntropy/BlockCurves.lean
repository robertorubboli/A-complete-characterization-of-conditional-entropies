import ConditionalEntropy.BlockEstimates
import ConditionalEntropy.SignedLineCalculus
import ConditionalEntropy.CompactUniform

/-!
# Scalar curves attached to a finite block family

This module introduces the total logarithmic, norm-free, and mass curves used
by the localization proof.  It also records the exact first two logarithmic
mass derivatives at the block base point.  Those identities are purely finite
calculus and do not use a localization or dominated-convergence hypothesis.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

/-- Iterated derivatives of the logarithmic signed column curve. -/
def blockLogKernel {J : ℕ} (mu : SignedMeasure Param) (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (q : ℕ) : ℝ := by
  letI := blockCarrierNonempty B n
  exact iteratedDeriv (signedLogPhiLine mu (blockLineData B n u)) q 0

/-- Iterated derivatives of the norm-free signed entropy curve. -/
def blockGKernel {J : ℕ} (mu : SignedMeasure Param) (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (q : ℕ) : ℝ := by
  letI := blockCarrierNonempty B n
  exact iteratedDeriv (integratedEntropyLine mu (blockLineData B n u)) q 0

/-- Total mass of the raw multiplicative block line. -/
def blockMass {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) (lambda : ℝ) : ℝ := by
  letI := blockCarrierNonempty B n
  exact ∑ i : BlockCarrier B n, blockLineRaw B n u lambda i

/-- Iterated derivatives of the logarithmic block mass. -/
def blockLogMassKernel {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) (q : ℕ) : ℝ :=
  iteratedDeriv (fun lambda ↦ Real.log (blockMass B n u lambda)) q 0

/-- The signed exponential column curve, with the line wrapper totalized away
from its positive interval. -/
def blockPhiCurve {J : ℕ} (mu : SignedMeasure Param) (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (lambda : ℝ) : ℝ := by
  letI := blockCarrierNonempty B n
  exact PhiSigned mu (lineConeTotal (blockLineData B n u) lambda)

/-- The norm-free signed entropy curve, with the positive-cone line wrapper
totalized away from its positive interval. -/
def blockGCurve {J : ℕ} (mu : SignedMeasure Param) (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (lambda : ℝ) : ℝ := by
  letI := blockCarrierNonempty B n
  exact GSigned mu (linePosConeTotal (blockLineData B n u) lambda)

/-- On the positive interval the total norm-free curve is the integrated
entropy line. -/
theorem blockGCurve_of_positive {J : ℕ} (mu : SignedMeasure Param)
    (B : BlockData J) (n : ℕ) (u : Fin (J + 1) → ℝ) {lambda : ℝ}
    (h : LinePositive (blockLineData B n u) lambda) :
    letI := blockCarrierNonempty B n
    blockGCurve mu B n u lambda =
      integratedEntropyLine mu (blockLineData B n u) lambda := by
  letI := blockCarrierNonempty B n
  have hb := signedLineColumnBridge mu (blockLineData B n u) h
  unfold blockGCurve
  rw [hb.2.2.2.2.2]
  exact hb.2.1.symm

/-- Positivity of the signed exponential block curve throughout the positive
line interval. -/
theorem blockPhiCurve_pos_of_positive {J : ℕ} (mu : SignedMeasure Param)
    (B : BlockData J) (n : ℕ) (u : Fin (J + 1) → ℝ) {lambda : ℝ}
    (h : LinePositive (blockLineData B n u) lambda) :
    0 < blockPhiCurve mu B n u lambda := by
  letI := blockCarrierNonempty B n
  have hb := signedLineColumnBridge mu (blockLineData B n u) h
  unfold blockPhiCurve
  rw [hb.2.2.2.2.1]
  exact hb.2.2.1

/-- On the positive interval, the logarithm of the total exponential curve is
the additive signed logarithmic entropy line. -/
theorem log_blockPhiCurve_of_positive {J : ℕ} (mu : SignedMeasure Param)
    (B : BlockData J) (n : ℕ) (u : Fin (J + 1) → ℝ) {lambda : ℝ}
    (h : LinePositive (blockLineData B n u) lambda) :
    letI := blockCarrierNonempty B n
    Real.log (blockPhiCurve mu B n u lambda) =
      signedLogPhiLine mu (blockLineData B n u) lambda := by
  letI := blockCarrierNonempty B n
  have hb := signedLineColumnBridge mu (blockLineData B n u) h
  unfold blockPhiCurve
  rw [hb.2.2.2.2.1]
  exact hb.2.2.2.1.symm

theorem blockPhiCurve_zero_pos {J : ℕ} (mu : SignedMeasure Param)
    (B : BlockData J) (n : ℕ) (u : Fin (J + 1) → ℝ) :
    0 < blockPhiCurve mu B n u 0 :=
  blockPhiCurve_pos_of_positive mu B n u (linePositiveZero _)

@[simp] theorem blockLogKernel_zero {J : ℕ} (mu : SignedMeasure Param)
    (B : BlockData J) (n : ℕ) (u : Fin (J + 1) → ℝ) :
    letI := blockCarrierNonempty B n
    blockLogKernel mu B n u 0 =
      signedLogPhiLine mu (blockLineData B n u) 0 := by
  letI := blockCarrierNonempty B n
  rfl

@[simp] theorem blockGKernel_zero {J : ℕ} (mu : SignedMeasure Param)
    (B : BlockData J) (n : ℕ) (u : Fin (J + 1) → ℝ) :
    letI := blockCarrierNonempty B n
    blockGKernel mu B n u 0 =
      integratedEntropyLine mu (blockLineData B n u) 0 := by
  letI := blockCarrierNonempty B n
  rfl

/-- The block mass is definitionally the mass of the underlying positive line. -/
theorem blockMass_eq_lineMass {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) (lambda : ℝ) :
    blockMass B n u lambda = lineMass (blockLineData B n u) lambda := by
  rfl

/-- Exact blockwise expansion of the raw mass. -/
theorem blockMass_eq_sum {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) (lambda : ℝ) :
    blockMass B n u lambda =
      ∑ j, (blockCount B n j : ℝ) *
        Real.rpow (blockScale n) (B.a j) * (1 + u j * lambda) := by
  letI := blockCarrierNonempty B n
  change (∑ i : Σ j, Fin (blockCount B n j),
      Real.rpow (blockScale n) (B.a i.1) * (1 + u i.1 * lambda)) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  simp
  ring

/-- The mass at the base point is strictly positive. -/
theorem blockMass_zero_pos {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) : 0 < blockMass B n u 0 := by
  letI := blockCarrierNonempty B n
  rw [blockMass_eq_lineMass]
  exact lineMass_pos (blockLineData B n u) (linePositiveZero _)

/-- First logarithmic mass derivative at the base point. -/
theorem blockLogMassKernel_one {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) :
    blockLogMassKernel B n u 1 = blockEscortMean B n 1 u := by
  letI := blockCarrierNonempty B n
  unfold blockLogMassKernel
  change deriv (fun lambda ↦ Real.log (lineMass (blockLineData B n u) lambda)) 0 = _
  rw [(hasDerivAt_log_lineMass (blockLineData B n u) (linePositiveZero _)).deriv,
    escortMean_blockLine_zero]

/-- Second logarithmic mass derivative at the base point. -/
theorem blockLogMassKernel_two {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) :
    blockLogMassKernel B n u 2 = -(blockEscortMean B n 1 u) ^ 2 := by
  letI := blockCarrierNonempty B n
  unfold blockLogMassKernel
  change secondDeriv (fun lambda ↦
    Real.log (lineMass (blockLineData B n u) lambda)) 0 = _
  unfold secondDeriv
  let L := blockLineData B n u
  have hposNhd : ∀ᶠ lambda in 𝓝 (0 : ℝ), LinePositive L lambda := by
    exact (isOpen_setOf_linePositive L).mem_nhds (linePositiveZero L)
  have hderiv : deriv (fun lambda ↦ Real.log (lineMass L lambda)) =ᶠ[𝓝 0]
      escortMean L 1 := by
    filter_upwards [hposNhd] with lambda hlambda
    exact (hasDerivAt_log_lineMass L hlambda).deriv
  have hmean := hasDerivAt_escortMean L (a := (1 : ℝ)) zero_lt_one
    (linePositiveZero L)
  have hmean' : HasDerivAt (escortMean L 1)
      (-(escortMean L 1 0) ^ 2) 0 := by
    convert hmean using 1
    ring
  rw [(hmean'.congr_of_eventuallyEq hderiv).deriv,
    escortMean_blockLine_zero]

/-- The first logarithmic mass kernel is a continuous linear finite sum in
the block velocity. -/
theorem continuous_blockLogMassKernel_one {J : ℕ} (B : BlockData J) (n : ℕ) :
    Continuous (fun u : Fin (J + 1) → ℝ ↦ blockLogMassKernel B n u 1) := by
  simp_rw [blockLogMassKernel_one, blockEscortMean]
  fun_prop

/-- The second logarithmic mass kernel is a continuous quadratic finite sum. -/
theorem continuous_blockLogMassKernel_two {J : ℕ} (B : BlockData J) (n : ℕ) :
    Continuous (fun u : Fin (J + 1) → ℝ ↦ blockLogMassKernel B n u 2) := by
  simp_rw [blockLogMassKernel_two, blockEscortMean]
  fun_prop

/-- Literal continuity interface for all derivative orders at most two. -/
theorem blockLogMassKernelContinuous {J : ℕ} (B : BlockData J) (n q : ℕ)
    (hq : q ≤ 2) :
    Continuous (fun u : Fin (J + 1) → ℝ ↦ blockLogMassKernel B n u q) := by
  interval_cases q
  · unfold blockLogMassKernel
    simp only [iteratedDeriv_zero]
    rw [show (fun u : Fin (J + 1) → ℝ ↦
        Real.log (blockMass B n u 0)) =
        fun _ ↦ Real.log (blockMass B n 0 0) by
      funext u
      congr 1
      rw [blockMass_eq_sum, blockMass_eq_sum]
      simp]
    exact continuous_const
  · exact continuous_blockLogMassKernel_one B n
  · exact continuous_blockLogMassKernel_two B n

/-! ## Uniform concentration of the logarithmic mass derivatives -/

/-- A block which uniquely maximizes the order-one exponent captures all of
the order-one escort mass as the scale tends to infinity. -/
theorem tendsto_blockOutsideMass_of_unique {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1))
    (hk : ∀ j : Fin (J + 1), j ≠ k →
      blockExponent B j 1 < blockExponent B k 1) :
    Tendsto (fun n : ℕ ↦
      ∑ j ∈ Finset.univ.erase k, blockEscort B n j 1)
      atTop (𝓝 0) := by
  have hterm : ∀ j ∈ Finset.univ.erase k,
      Tendsto (fun n : ℕ ↦ blockEscort B n j 1) atTop (𝓝 0) := by
    intro j hj
    have hjk : j ≠ k := Finset.ne_of_mem_erase hj
    let eta : ℝ := blockExponent B k 1 - blockExponent B j 1
    have heta : 0 < eta := sub_pos.mpr (hk j hjk)
    have hdecay : Tendsto (fun n : ℕ ↦
        Real.rpow (blockScale n) (-eta)) atTop (𝓝 0) := by
      exact (tendsto_rpow_neg_atTop heta).comp tendsto_blockScale_atTop
    have htwo : Tendsto (fun n : ℕ ↦
        2 * Real.rpow (blockScale n) (-eta)) atTop (𝓝 0) := by
      simpa using hdecay.const_mul 2
    apply squeeze_zero
    · exact fun n ↦ blockEscort_nonneg B n j 1
    · intro n
      exact blockEscort_le_two_mul_decay B n k j 1 eta le_rfl
    · exact htwo
  simpa using tendsto_finsetSum (Finset.univ.erase k) hterm

/-- Compactness supplies one absolute coordinate bound for every velocity in
the compact family. -/
theorem exists_uniform_coordinate_bound {J : ℕ}
    (K : Set (Fin (J + 1) → ℝ)) (hK : IsCompact K) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ u ∈ K, ∀ j, |u j| ≤ U := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall
    (0 : Fin (J + 1) → ℝ)
  let U := max R 0
  refine ⟨U, le_max_right _ _, ?_⟩
  intro u hu j
  have huBall := hR hu
  have hnorm : ‖u‖ ≤ R := by
    simpa [dist_zero_right] using huBall
  calc
    |u j| = ‖u j‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖u‖ := norm_le_pi_norm u j
    _ ≤ R := hnorm
    _ ≤ U := le_max_left _ _

/-- Uniform convergence of the first logarithmic mass derivative on a compact
velocity family. -/
theorem compactUniform_blockLogMassKernel_one {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1))
    (hk : ∀ j : Fin (J + 1), j ≠ k →
      blockExponent B j 1 < blockExponent B k 1)
    (K : Set (Fin (J + 1) → ℝ)) (hK0 : K.Nonempty) (hK : IsCompact K) :
    CompactUniformConverges K
      (fun n u ↦ blockLogMassKernel B n u 1) (fun u ↦ u k) := by
  obtain ⟨U, hU, hbound⟩ := exists_uniform_coordinate_bound K hK
  let outside : ℕ → ℝ := fun n ↦
    ∑ j ∈ Finset.univ.erase k, blockEscort B n j 1
  have hout : Tendsto outside atTop (𝓝 0) :=
    tendsto_blockOutsideMass_of_unique B k hk
  have hmajor : Tendsto (fun n ↦ (2 * U) * outside n) atTop (𝓝 0) := by
    simpa using hout.const_mul (2 * U)
  unfold CompactUniformConverges
  apply squeeze_zero
  · intro n
    exact compactUniformError_nonneg K hK0 hK
      (fun m u ↦ blockLogMassKernel B m u 1) (fun u ↦ u k) n
      (continuous_blockLogMassKernel_one B n).continuousOn
      (continuous_apply k).continuousOn
  · intro n
    unfold compactUniformError
    apply csSup_le
    · obtain ⟨u, hu⟩ := hK0
      exact ⟨|blockLogMassKernel B n u 1 - u k|, ⟨u, hu, rfl⟩⟩
    · intro z hz
      rcases hz with ⟨u, hu, rfl⟩
      dsimp only
      rw [blockLogMassKernel_one]
      simpa only [outside] using
        abs_blockEscortMean_sub_le_outside B n 1 k u U (hbound u hu)
  · exact hmajor

/-- Uniform convergence of the second logarithmic mass derivative on a compact
velocity family. -/
theorem compactUniform_blockLogMassKernel_two {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1))
    (hk : ∀ j : Fin (J + 1), j ≠ k →
      blockExponent B j 1 < blockExponent B k 1)
    (K : Set (Fin (J + 1) → ℝ)) (hK0 : K.Nonempty) (hK : IsCompact K) :
    CompactUniformConverges K
      (fun n u ↦ blockLogMassKernel B n u 2) (fun u ↦ -(u k) ^ 2) := by
  obtain ⟨U, hU, hbound⟩ := exists_uniform_coordinate_bound K hK
  let outside : ℕ → ℝ := fun n ↦
    ∑ j ∈ Finset.univ.erase k, blockEscort B n j 1
  have hout : Tendsto outside atTop (𝓝 0) :=
    tendsto_blockOutsideMass_of_unique B k hk
  have hmajor : Tendsto (fun n ↦ (4 * U ^ 2) * outside n) atTop (𝓝 0) := by
    simpa using hout.const_mul (4 * U ^ 2)
  unfold CompactUniformConverges
  apply squeeze_zero
  · intro n
    exact compactUniformError_nonneg K hK0 hK
      (fun m u ↦ blockLogMassKernel B m u 2) (fun u ↦ -(u k) ^ 2) n
      (continuous_blockLogMassKernel_two B n).continuousOn
      ((continuous_apply k).pow 2).neg.continuousOn
  · intro n
    unfold compactUniformError
    apply csSup_le
    · obtain ⟨u, hu⟩ := hK0
      exact ⟨|blockLogMassKernel B n u 2 - -(u k) ^ 2|, ⟨u, hu, rfl⟩⟩
    · intro z hz
      rcases hz with ⟨u, hu, rfl⟩
      dsimp only
      rw [blockLogMassKernel_two]
      have hmean := abs_blockEscortMean_sub_le_outside B n 1 k u U (hbound u hu)
      have hmeanAbs := abs_blockEscortMean_le B n 1 u U (hbound u hu)
      have huk := hbound u hu k
      calc
        |-blockEscortMean B n 1 u ^ 2 - -u k ^ 2| =
            |blockEscortMean B n 1 u ^ 2 - u k ^ 2| := by
              rw [show -blockEscortMean B n 1 u ^ 2 - -u k ^ 2 =
                -(blockEscortMean B n 1 u ^ 2 - u k ^ 2) by ring, abs_neg]
        _ =
            |blockEscortMean B n 1 u - u k| *
              |blockEscortMean B n 1 u + u k| := by
                rw [← abs_mul]
                congr 1
                ring
        _ ≤ ((2 * U) * outside n) * (2 * U) := by
          apply mul_le_mul hmean
          · calc
              |blockEscortMean B n 1 u + u k| ≤
                  |blockEscortMean B n 1 u| + |u k| := abs_add_le _ _
              _ ≤ 2 * U := by linarith
          · exact abs_nonneg _
          · exact mul_nonneg (mul_nonneg (by norm_num) hU)
              (Finset.sum_nonneg fun j _ ↦ blockEscort_nonneg B n j 1)
        _ = (4 * U ^ 2) * outside n := by ring
  · exact hmajor

/-- The literal pair of compact-uniform logarithmic mass limits. -/
theorem blockLogMassKernelLimits {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1))
    (hk : ∀ j : Fin (J + 1), j ≠ k →
      blockExponent B j 1 < blockExponent B k 1)
    (K : Set (Fin (J + 1) → ℝ)) (hK0 : K.Nonempty) (hK : IsCompact K) :
    CompactUniformConverges K
        (fun n u ↦ blockLogMassKernel B n u 1) (fun u ↦ u k) ∧
      CompactUniformConverges K
        (fun n u ↦ blockLogMassKernel B n u 2) (fun u ↦ -(u k) ^ 2) :=
  ⟨compactUniform_blockLogMassKernel_one B k hk K hK0 hK,
    compactUniform_blockLogMassKernel_two B k hk K hK0 hK⟩

end ConditionalEntropy
