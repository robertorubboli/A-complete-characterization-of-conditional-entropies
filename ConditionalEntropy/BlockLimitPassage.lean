import ConditionalEntropy.BlockEstimates
import ConditionalEntropy.UniformSignedDCT
import ConditionalEntropy.SpecialBlockData
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Uniform passage to finite-block limits

This module contains the pointwise block-limit kernels and the uniform signed
integral limit package used by the two- and three-block localization proofs.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

/-- First pointwise limit kernel of a finite block family. -/
def blockLimitFirst {J : ℕ} (k : Param → Fin (J + 1))
    (u : Fin (J + 1) → ℝ) (beta : Param) : ℝ :=
  singularWeight beta * (u (k beta) - u (k 1))

/-- Second pointwise limit kernel of a finite block family. -/
def blockLimitSecond {J : ℕ} (k : Param → Fin (J + 1))
    (u : Fin (J + 1) → ℝ) (beta : Param) : ℝ :=
  singularWeight beta * ((u (k 1)) ^ 2 - (u (k beta)) ^ 2)

@[simp] theorem blockLimitFirst_one {J : ℕ} (k : Param → Fin (J + 1))
    (u : Fin (J + 1) → ℝ) : blockLimitFirst k u 1 = 0 := by
  simp [blockLimitFirst]

@[simp] theorem blockLimitSecond_one {J : ℕ} (k : Param → Fin (J + 1))
    (u : Fin (J + 1) → ℝ) : blockLimitSecond k u 1 = 0 := by
  simp [blockLimitSecond]

theorem measurable_blockLimitFirst {J : ℕ} {k : Param → Fin (J + 1)}
    (hk : Measurable k) (u : Fin (J + 1) → ℝ) :
    Measurable (blockLimitFirst k u) := by
  unfold blockLimitFirst
  have hu : Measurable u := measurable_of_finite _
  exact measurable_singularWeight.mul
    ((hu.comp hk).sub (hu.comp measurable_const))

theorem measurable_blockLimitSecond {J : ℕ} {k : Param → Fin (J + 1)}
    (hk : Measurable k) (u : Fin (J + 1) → ℝ) :
    Measurable (blockLimitSecond k u) := by
  unfold blockLimitSecond
  have hu : Measurable u := measurable_of_finite _
  exact measurable_singularWeight.mul
    (((hu.comp measurable_const).pow_const 2).sub ((hu.comp hk).pow_const 2))

theorem continuous_blockLimitFirst_velocity {J : ℕ}
    (k : Param → Fin (J + 1)) (beta : Param) :
    Continuous (fun u : Fin (J + 1) → ℝ => blockLimitFirst k u beta) := by
  unfold blockLimitFirst
  fun_prop

theorem continuous_blockLimitSecond_velocity {J : ℕ}
    (k : Param → Fin (J + 1)) (beta : Param) :
    Continuous (fun u : Fin (J + 1) → ℝ => blockLimitSecond k u beta) := by
  unfold blockLimitSecond
  fun_prop

private theorem continuous_blockContribution_order {J : ℕ} (B : BlockData J)
    (n : ℕ) (j : Fin (J + 1)) : Continuous (blockContribution B n j) := by
  unfold blockContribution
  exact continuous_const.mul (Real.continuous_const_rpow
    (Real.rpow_pos_of_pos (blockScale_pos n) (B.a j)).ne')

private theorem continuous_blockEscort_order {J : ℕ} (B : BlockData J)
    (n : ℕ) (j : Fin (J + 1)) : Continuous (blockEscort B n j) := by
  unfold blockEscort
  have hden : Continuous (fun alpha =>
      ∑ l, blockContribution B n l alpha) := by
    simpa using continuous_finsetSum Finset.univ
      (fun l _ => continuous_blockContribution_order B n l)
  apply Continuous.div
  · exact continuous_blockContribution_order B n j
  · exact hden
  · intro alpha
    exact (sum_blockContribution_pos B n alpha).ne'

private theorem continuous_blockEscortMean_order {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) :
    Continuous (fun alpha => blockEscortMean B n alpha u) := by
  unfold blockEscortMean
  simpa using continuous_finsetSum Finset.univ
    (fun j _ => (continuous_blockEscort_order B n j).mul continuous_const)

private theorem continuous_blockEscortSecond_order {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) :
    Continuous (fun alpha => blockEscortSecond B n alpha u) := by
  unfold blockEscortSecond
  simpa using continuous_finsetSum Finset.univ
    (fun j _ => (continuous_blockEscort_order B n j).mul continuous_const)

private theorem continuous_blockEscortVar_order {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) :
    Continuous (fun alpha => blockEscortVar B n alpha u) := by
  unfold blockEscortVar
  exact (continuous_blockEscortSecond_order B n u).sub
    ((continuous_blockEscortMean_order B n u).pow 2)

private theorem continuous_blockEscortMean_velocity {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) :
    Continuous (fun u : Fin (J + 1) → ℝ => blockEscortMean B n alpha u) := by
  unfold blockEscortMean
  fun_prop

private theorem continuous_blockEscortSecond_velocity {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) :
    Continuous (fun u : Fin (J + 1) → ℝ => blockEscortSecond B n alpha u) := by
  unfold blockEscortSecond
  fun_prop

private theorem continuous_blockEscortVar_velocity {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) :
    Continuous (fun u : Fin (J + 1) → ℝ => blockEscortVar B n alpha u) := by
  unfold blockEscortVar
  exact (continuous_blockEscortSecond_velocity B n alpha).sub
    ((continuous_blockEscortMean_velocity B n alpha).pow 2)

@[simp] private theorem blockKernelFirst_zero {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) : blockKernelFirst B n u 0 = 0 := by
  letI := blockCarrierNonempty B n
  exact entropyLineFirst_zero (blockLineData B n u) (linePositiveZero _)

@[simp] private theorem blockKernelSecond_zero {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) : blockKernelSecond B n u 0 = 0 := by
  letI := blockCarrierNonempty B n
  exact entropyLineSecond_zero (blockLineData B n u) (linePositiveZero _)

private theorem blockKernelFirst_eq_piecewise {J : ℕ} (B : BlockData J)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop)
    (n : ℕ) (u : Fin (J + 1) → ℝ) :
    blockKernelFirst B n u = fun beta =>
      if beta = (⊤ : Param) then blockEscortMean B n 1 u - u jTop
      else if beta = (0 : Param) then 0
      else if beta = (1 : Param) then blockKernelFirst B n u 1
      else singularWeight beta *
        (blockEscortMean B n (ENNReal.toReal beta) u -
          blockEscortMean B n 1 u) := by
  funext beta
  by_cases hbetaTop : beta = (⊤ : Param)
  · subst beta
    simp [blockKernelFirst_top_eq B jTop hTop]
  rw [if_neg hbetaTop]
  by_cases hbetaZero : beta = (0 : Param)
  · subst beta
    simp
  rw [if_neg hbetaZero]
  by_cases hbetaOne : beta = (1 : Param)
  · subst beta
    simp
  rw [if_neg hbetaOne]
  have hrealPos : 0 < ENNReal.toReal beta := by
    exact ENNReal.toReal_pos hbetaZero hbetaTop
  have hrealOne : ENNReal.toReal beta ≠ 1 := by
    intro h
    have hback := finiteParam_paramToReal beta hbetaTop
    rw [show paramToReal beta hbetaTop = ENNReal.toReal beta by rfl, h,
      finiteParam_one] at hback
    exact hbetaOne hback.symm
  have hback := finiteParam_paramToReal beta hbetaTop
  rw [show paramToReal beta hbetaTop = ENNReal.toReal beta by rfl] at hback
  rw [← hback, blockKernelFirst_finite B n u hrealPos hrealOne]
  simp only [finiteParam, ENNReal.toReal_ofReal hrealPos.le]

private theorem blockKernelSecond_eq_piecewise {J : ℕ} (B : BlockData J)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop)
    (n : ℕ) (u : Fin (J + 1) → ℝ) :
    blockKernelSecond B n u = fun beta =>
      if beta = (⊤ : Param) then (u jTop) ^ 2 - (blockEscortMean B n 1 u) ^ 2
      else if beta = (0 : Param) then 0
      else if beta = (1 : Param) then blockKernelSecond B n u 1
      else -ENNReal.toReal beta * blockEscortVar B n (ENNReal.toReal beta) u +
        singularWeight beta *
          ((blockEscortMean B n 1 u) ^ 2 -
            (blockEscortMean B n (ENNReal.toReal beta) u) ^ 2) := by
  funext beta
  by_cases hbetaTop : beta = (⊤ : Param)
  · subst beta
    rw [if_pos rfl, blockKernelSecond_top_eq B jTop hTop]
  rw [if_neg hbetaTop]
  by_cases hbetaZero : beta = (0 : Param)
  · subst beta
    simp
  rw [if_neg hbetaZero]
  by_cases hbetaOne : beta = (1 : Param)
  · subst beta
    simp
  rw [if_neg hbetaOne]
  have hrealPos : 0 < ENNReal.toReal beta := by
    exact ENNReal.toReal_pos hbetaZero hbetaTop
  have hrealOne : ENNReal.toReal beta ≠ 1 := by
    intro h
    have hback := finiteParam_paramToReal beta hbetaTop
    rw [show paramToReal beta hbetaTop = ENNReal.toReal beta by rfl, h,
      finiteParam_one] at hback
    exact hbetaOne hback.symm
  have hback := finiteParam_paramToReal beta hbetaTop
  rw [show paramToReal beta hbetaTop = ENNReal.toReal beta by rfl] at hback
  rw [← hback, blockKernelSecond_finite B n u hrealPos hrealOne]
  simp only [finiteParam, ENNReal.toReal_ofReal hrealPos.le]

theorem measurable_blockKernelFirst {J : ℕ} (B : BlockData J)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop)
    (n : ℕ) (u : Fin (J + 1) → ℝ) :
    Measurable (blockKernelFirst B n u) := by
  rw [blockKernelFirst_eq_piecewise B jTop hTop n u]
  have hmean : Measurable (fun beta : Param =>
      blockEscortMean B n (ENNReal.toReal beta) u) :=
    (continuous_blockEscortMean_order B n u).measurable.comp
      ENNReal.measurable_toReal
  exact Measurable.ite (measurableSet_singleton (⊤ : Param)) measurable_const <|
    Measurable.ite (measurableSet_singleton (0 : Param)) measurable_const <|
      Measurable.ite (measurableSet_singleton (1 : Param)) measurable_const <|
        measurable_singularWeight.mul (hmean.sub measurable_const)

theorem measurable_blockKernelSecond {J : ℕ} (B : BlockData J)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop)
    (n : ℕ) (u : Fin (J + 1) → ℝ) :
    Measurable (blockKernelSecond B n u) := by
  rw [blockKernelSecond_eq_piecewise B jTop hTop n u]
  have hreal : Measurable (fun beta : Param => ENNReal.toReal beta) :=
    ENNReal.measurable_toReal
  have hmean : Measurable (fun beta : Param =>
      blockEscortMean B n (ENNReal.toReal beta) u) :=
    (continuous_blockEscortMean_order B n u).measurable.comp hreal
  have hvar : Measurable (fun beta : Param =>
      blockEscortVar B n (ENNReal.toReal beta) u) :=
    (continuous_blockEscortVar_order B n u).measurable.comp hreal
  exact Measurable.ite (measurableSet_singleton (⊤ : Param)) measurable_const <|
    Measurable.ite (measurableSet_singleton (0 : Param)) measurable_const <|
      Measurable.ite (measurableSet_singleton (1 : Param)) measurable_const <|
        hreal.neg.mul hvar |>.add <|
          measurable_singularWeight.mul
            ((measurable_const.pow_const 2).sub (hmean.pow_const 2))

private theorem continuous_blockKernelFirst_velocity {J : ℕ} (B : BlockData J)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop)
    (n : ℕ) (beta : Param) :
    Continuous (fun u : Fin (J + 1) → ℝ => blockKernelFirst B n u beta) := by
  by_cases hbetaTop : beta = (⊤ : Param)
  · subst beta
    simp_rw [blockKernelFirst_top_eq B jTop hTop]
    exact (continuous_blockEscortMean_velocity B n 1).sub (continuous_apply jTop)
  by_cases hbetaZero : beta = (0 : Param)
  · subst beta
    simpa using (continuous_const : Continuous (fun _ : Fin (J + 1) → ℝ => (0 : ℝ)))
  by_cases hbetaOne : beta = (1 : Param)
  · subst beta
    simp_rw [blockKernelFirst_one, deriv_blockEscortMean_order]
    exact (continuous_finsetSum Finset.univ fun j _ =>
      continuous_const.mul (continuous_apply j)).neg
  have hrealPos : 0 < ENNReal.toReal beta := by
    exact ENNReal.toReal_pos hbetaZero hbetaTop
  have hrealOne : ENNReal.toReal beta ≠ 1 := by
    intro h
    have hback := finiteParam_paramToReal beta hbetaTop
    rw [show paramToReal beta hbetaTop = ENNReal.toReal beta by rfl, h,
      finiteParam_one] at hback
    exact hbetaOne hback.symm
  have hback := finiteParam_paramToReal beta hbetaTop
  rw [show paramToReal beta hbetaTop = ENNReal.toReal beta by rfl] at hback
  rw [← hback]
  simp_rw [blockKernelFirst_finite B n _ hrealPos hrealOne]
  exact continuous_const.mul
    ((continuous_blockEscortMean_velocity B n _).sub
      (continuous_blockEscortMean_velocity B n 1))

private theorem continuous_blockKernelSecond_velocity {J : ℕ} (B : BlockData J)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop)
    (n : ℕ) (beta : Param) :
    Continuous (fun u : Fin (J + 1) → ℝ => blockKernelSecond B n u beta) := by
  by_cases hbetaTop : beta = (⊤ : Param)
  · subst beta
    simp_rw [blockKernelSecond_top_eq B jTop hTop]
    exact ((continuous_apply jTop).pow 2).sub
      ((continuous_blockEscortMean_velocity B n 1).pow 2)
  by_cases hbetaZero : beta = (0 : Param)
  · subst beta
    simpa using (continuous_const : Continuous (fun _ : Fin (J + 1) → ℝ => (0 : ℝ)))
  by_cases hbetaOne : beta = (1 : Param)
  · subst beta
    simp_rw [blockKernelSecond_one]
    exact (continuous_blockEscortVar_velocity B n 1).neg.sub
      ((continuous_const.mul (continuous_blockEscortMean_velocity B n 1)).mul
        (continuous_blockKernelFirst_velocity B jTop hTop n 1))
  have hrealPos : 0 < ENNReal.toReal beta := by
    exact ENNReal.toReal_pos hbetaZero hbetaTop
  have hrealOne : ENNReal.toReal beta ≠ 1 := by
    intro h
    have hback := finiteParam_paramToReal beta hbetaTop
    rw [show paramToReal beta hbetaTop = ENNReal.toReal beta by rfl, h,
      finiteParam_one] at hback
    exact hbetaOne hback.symm
  have hback := finiteParam_paramToReal beta hbetaTop
  rw [show paramToReal beta hbetaTop = ENNReal.toReal beta by rfl] at hback
  rw [← hback]
  simp_rw [blockKernelSecond_finite B n _ hrealPos hrealOne]
  exact (continuous_const.neg.mul
      (continuous_blockEscortVar_velocity B n (ENNReal.toReal beta))).add
    (continuous_const.mul
      (((continuous_blockEscortMean_velocity B n 1).pow 2).sub
        ((continuous_blockEscortMean_velocity B n (ENNReal.toReal beta)).pow 2)))

private theorem exists_velocity_bound {J : ℕ}
    (K : Set (Fin (J + 1) → ℝ)) (hK : IsCompact K) (hK0 : K.Nonempty) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ u ∈ K, ∀ j, |u j| ≤ U := by
  have hbdd : BddAbove ((fun u : Fin (J + 1) → ℝ => ‖u‖) '' K) :=
    hK.bddAbove_image continuous_norm.continuousOn
  obtain ⟨U, hU⟩ := bddAbove_def.mp hbdd
  obtain ⟨u0, hu0⟩ := hK0
  have hU0 : 0 ≤ U :=
    (norm_nonneg u0).trans (hU _ ⟨u0, hu0, rfl⟩)
  refine ⟨U, hU0, ?_⟩
  intro u hu j
  calc
    |u j| = ‖u j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖u‖ := norm_le_pi_norm u j
    _ ≤ U := hU _ ⟨u, hu, rfl⟩

/-- The smallest positive exponent gap from a designated block at one
fixed order.  The designated coordinate receives the harmless value one. -/
private def pointExponentGap {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1)) (alpha : ℝ) : ℝ :=
  finMin (fun j : Fin (J + 1) =>
    if j = k then 1 else blockExponent B k alpha - blockExponent B j alpha)

private theorem pointExponentGap_pos {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1)) (alpha : ℝ)
    (hmax : ∀ j : Fin (J + 1), j ≠ k →
      blockExponent B j alpha < blockExponent B k alpha) :
    0 < pointExponentGap B k alpha := by
  obtain ⟨j, hj⟩ := finMin_mem
    (fun j : Fin (J + 1) =>
      if j = k then 1 else blockExponent B k alpha - blockExponent B j alpha)
  change 0 < finMin (fun j : Fin (J + 1) =>
    if j = k then 1 else blockExponent B k alpha - blockExponent B j alpha)
  rw [← hj]
  by_cases hjk : j = k
  · simp [hjk]
  · simp only [hjk, ↓reduceIte]
    exact sub_pos.mpr (hmax j hjk)

private theorem pointExponentGap_le {J : ℕ} (B : BlockData J)
    (k j : Fin (J + 1)) (alpha : ℝ) (hjk : j ≠ k) :
    pointExponentGap B k alpha ≤
      blockExponent B k alpha - blockExponent B j alpha := by
  have hle := finMin_le
    (fun l : Fin (J + 1) =>
      if l = k then 1 else blockExponent B k alpha - blockExponent B l alpha) j
  simpa only [pointExponentGap, hjk, ↓reduceIte] using hle

private theorem nearOneDominance {J : ℕ} (B : BlockData J)
    (T : Finset ℝ) (k : Param → Fin (J + 1))
    (hOne : 1 ∉ T)
    (hUnique : ∀ alpha : ℝ, 0 ≤ alpha → alpha ∉ T →
      ∀ j : Fin (J + 1), j ≠ k (finiteParam alpha) →
        blockExponent B j alpha <
          blockExponent B (k (finiteParam alpha)) alpha) :
    ∃ delta eta : ℝ,
      0 < delta ∧ delta < 1 ∧ 0 < eta ∧
      (∀ alpha ∈ Icc (1 - delta) (1 + delta),
        ∀ j : Fin (J + 1), j ≠ k 1 →
          eta ≤ blockExponent B (k 1) alpha - blockExponent B j alpha) ∧
      (∀ alpha ∈ Icc (1 - delta) (1 + delta), alpha ∉ T →
        k (finiteParam alpha) = k 1) := by
  let k1 := k 1
  have hmax1 : ∀ j : Fin (J + 1), j ≠ k1 →
      blockExponent B j 1 < blockExponent B k1 1 := by
    intro j hj
    dsimp only [k1] at hj ⊢
    have hj' : j ≠ k (finiteParam 1) := by simpa only [finiteParam_one] using hj
    simpa only [finiteParam_one] using hUnique 1 zero_le_one hOne j hj'
  let gap := pointExponentGap B k1 1
  let D := blockAmplitudeDiameter B
  let delta := min (1 / 2 : ℝ) (gap / (2 * (D + 1)))
  let eta := gap / 2
  have hgap : 0 < gap := by
    simpa only [gap] using pointExponentGap_pos B k1 1 hmax1
  have hD : 0 ≤ D := by
    simpa only [D] using blockAmplitudeDiameter_nonneg B
  have hden : 0 < 2 * (D + 1) := by positivity
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min (by norm_num) (div_pos hgap hden)
  have hdeltaOne : delta < 1 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have heta : 0 < eta := by dsimp only [eta]; linarith
  have hdeltaMul : 2 * (D + 1) * delta ≤ gap := by
    have hle : delta ≤ gap / (2 * (D + 1)) := by
      dsimp only [delta]
      exact min_le_right _ _
    simpa only [mul_comm] using (le_div_iff₀ hden).mp hle
  have hDdelta : D * delta ≤ gap / 2 := by
    nlinarith [mul_nonneg hD hdelta.le]
  have hnearGap : ∀ alpha ∈ Icc (1 - delta) (1 + delta),
      ∀ j : Fin (J + 1), j ≠ k1 →
        eta ≤ blockExponent B k1 alpha - blockExponent B j alpha := by
    intro alpha halpha j hj
    have hbase := pointExponentGap_le B k1 j 1 hj
    have hamp : |B.a k1 - B.a j| ≤ D := by
      rw [abs_sub_comm]
      simpa only [D] using abs_amplitude_sub_le_diameter B j k1
    have halphaAbs : |alpha - 1| ≤ delta := by
      rw [abs_le]
      constructor <;> linarith [halpha.1, halpha.2]
    have hprodAbs : |(B.a k1 - B.a j) * (alpha - 1)| ≤ D * delta := by
      rw [abs_mul]
      exact mul_le_mul hamp halphaAbs (abs_nonneg _) hD
    have hprodLower : -(D * delta) ≤
        (B.a k1 - B.a j) * (alpha - 1) :=
      (abs_le.mp hprodAbs).1
    dsimp only [eta, gap]
    unfold blockExponent at hbase ⊢
    nlinarith
  refine ⟨delta, eta, hdelta, hdeltaOne, heta, ?_, ?_⟩
  · simpa only [k1] using hnearGap
  · intro alpha halpha hAlphaT
    have hAlphaPos : 0 ≤ alpha := by linarith [halpha.1, hdeltaOne]
    let ka := k (finiteParam alpha)
    by_contra hne
    have hleft : blockExponent B (k1) alpha < blockExponent B ka alpha := by
      simpa only [ka] using hUnique alpha hAlphaPos hAlphaT k1 (Ne.symm hne)
    have hnear := hnearGap alpha halpha ka hne
    have : blockExponent B ka alpha < blockExponent B k1 alpha := by
      linarith
    exact (not_lt_of_ge this.le) hleft

private theorem blockEscortVar_le_four_sq {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) (u : Fin (J + 1) → ℝ) (U : ℝ)
    (hU : 0 ≤ U) (hu : ∀ j, |u j| ≤ U) :
    blockEscortVar B n alpha u ≤ 4 * U ^ 2 := by
  have h := blockEscortVar_le_outside B n alpha 0 u U hU hu
  calc
    blockEscortVar B n alpha u ≤
        (4 * U ^ 2) *
          (∑ j ∈ Finset.univ.erase 0, blockEscort B n j alpha) := h
    _ ≤ (4 * U ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left (blockOutsideMass_le_one B n 0 alpha) (by positivity)
    _ = 4 * U ^ 2 := mul_one _

private theorem finiteKernelCrudeBounds {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (U A delta alpha : ℝ)
    (hU : 0 ≤ U) (hu : ∀ j, |u j| ≤ U)
    (hAlpha : 0 < alpha) (hAlphaA : alpha ≤ A)
    (hDelta : 0 < delta) (hAway : delta ≤ |alpha - 1|) :
    |blockKernelFirst B n u (finiteParam alpha)| ≤
        2 * U * (A / delta) ∧
      |blockKernelSecond B n u (finiteParam alpha)| ≤
        4 * A * U ^ 2 + 2 * U ^ 2 * (A / delta) := by
  have hOne : alpha ≠ 1 := by
    intro h
    subst alpha
    have : ¬delta ≤ 0 := not_le_of_gt hDelta
    exact this (by simpa using hAway)
  have hA : 0 ≤ A := hAlpha.le.trans hAlphaA
  have hW : 0 ≤ A / delta := div_nonneg hA hDelta.le
  have hWeight : |singularWeight (finiteParam alpha)| ≤ A / delta := by
    rw [singularWeight_finite hAlpha.le hOne, abs_div, abs_of_pos hAlpha,
      abs_sub_comm]
    exact (div_le_div_iff₀ (lt_of_lt_of_le hDelta hAway) hDelta).2
      (mul_le_mul hAlphaA hAway hDelta.le hA)
  have hMeanAlpha := abs_blockEscortMean_le B n alpha u U hu
  have hMeanOne := abs_blockEscortMean_le B n 1 u U hu
  have hMeanDiff :
      |blockEscortMean B n alpha u - blockEscortMean B n 1 u| ≤ 2 * U := by
    calc
      _ ≤ |blockEscortMean B n alpha u| +
          |blockEscortMean B n 1 u| := abs_sub _ _
      _ ≤ U + U := add_le_add hMeanAlpha hMeanOne
      _ = 2 * U := by ring
  have hSqDiff :
      |(blockEscortMean B n 1 u) ^ 2 -
          (blockEscortMean B n alpha u) ^ 2| ≤ 2 * U ^ 2 := by
    calc
      _ ≤ |(blockEscortMean B n 1 u) ^ 2| +
          |(blockEscortMean B n alpha u) ^ 2| := abs_sub _ _
      _ = (blockEscortMean B n 1 u) ^ 2 +
          (blockEscortMean B n alpha u) ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
      _ ≤ U ^ 2 + U ^ 2 := by
        exact add_le_add
          (sq_le_sq.mpr (by simpa only [abs_of_nonneg hU] using hMeanOne))
          (sq_le_sq.mpr (by simpa only [abs_of_nonneg hU] using hMeanAlpha))
      _ = 2 * U ^ 2 := by ring
  have hVar := blockEscortVar_le_four_sq B n alpha u U hU hu
  constructor
  · rw [blockKernelFirst_finite B n u hAlpha hOne, abs_mul]
    calc
      |singularWeight (finiteParam alpha)| *
          |blockEscortMean B n alpha u - blockEscortMean B n 1 u| ≤
          (A / delta) * (2 * U) :=
        mul_le_mul hWeight hMeanDiff (abs_nonneg _) hW
      _ = 2 * U * (A / delta) := by ring
  · rw [blockKernelSecond_finite B n u hAlpha hOne]
    calc
      |-alpha * blockEscortVar B n alpha u +
          singularWeight (finiteParam alpha) *
            ((blockEscortMean B n 1 u) ^ 2 -
              (blockEscortMean B n alpha u) ^ 2)| ≤
          |-alpha * blockEscortVar B n alpha u| +
            |singularWeight (finiteParam alpha) *
              ((blockEscortMean B n 1 u) ^ 2 -
                (blockEscortMean B n alpha u) ^ 2)| := abs_add_le _ _
      _ ≤ alpha * (4 * U ^ 2) + (A / delta) * (2 * U ^ 2) := by
        rw [abs_mul, abs_neg, abs_of_pos hAlpha,
          abs_of_nonneg (blockEscortVar_nonneg B n alpha u), abs_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hVar hAlpha.le)
          (mul_le_mul hWeight hSqDiff (abs_nonneg _) hW)
      _ ≤ A * (4 * U ^ 2) + (A / delta) * (2 * U ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_right hAlphaA (by positivity)) le_rfl
      _ = 4 * A * U ^ 2 + 2 * U ^ 2 * (A / delta) := by ring

private theorem exists_uniform_blockKernel_bound {J : ℕ} (B : BlockData J)
    (T : Finset ℝ) (k : Param → Fin (J + 1)) (jTop : Fin (J + 1))
    (hOne : 1 ∉ T)
    (hUnique : ∀ alpha : ℝ, 0 ≤ alpha → alpha ∉ T →
      ∀ j : Fin (J + 1), j ≠ k (finiteParam alpha) →
        blockExponent B j alpha <
          blockExponent B (k (finiteParam alpha)) alpha)
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop)
    (U : ℝ) (hU : 0 ≤ U) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (u : Fin (J + 1) → ℝ),
        (∀ j, |u j| ≤ U) → ∀ beta : Param,
          |blockKernelFirst B n u beta| ≤ C ∧
          |blockKernelSecond B n u beta| ≤ C := by
  obtain ⟨delta, eta, hdelta, hdeltaOne, heta, hnearGap, _hkNear⟩ :=
    nearOneDominance B T k hOne hUnique
  obtain ⟨Cnear, hCnear, hnear, hnearTendsto⟩ :=
    nearShannonDominant B (k 1) delta eta U hdelta hdeltaOne heta hU hnearGap
  have hnearBdd := hnearTendsto.bddAbove_range
  obtain ⟨Mnear, hMnear⟩ := bddAbove_def.mp hnearBdd
  have hMnear0 : 0 ≤ Mnear := by
    have hzero : 0 ≤ Cnear * (1 + Real.log (blockScale 0)) *
        Real.rpow (blockScale 0) (-eta) := by
      exact mul_nonneg
        (mul_nonneg hCnear (by
          have := log_blockScale_nonneg 0
          linarith))
        (Real.rpow_nonneg (blockScale_pos 0).le _)
    exact hzero.trans (hMnear _ ⟨0, rfl⟩)
  obtain ⟨A, gamma, Clarge, hA, _hgamma, hClarge, hlarge⟩ :=
    largeAlphaTail B jTop U hU hTop
  let Cfirst : ℝ := 2 * U * (A / delta)
  let Csecond : ℝ := 4 * A * U ^ 2 + 2 * U ^ 2 * (A / delta)
  let C : ℝ := Mnear + Clarge + Cfirst + Csecond
  have hA0 : 0 ≤ A := by linarith
  have hCfirst : 0 ≤ Cfirst := by dsimp only [Cfirst]; positivity
  have hCsecond : 0 ≤ Csecond := by
    dsimp only [Csecond]
    exact add_nonneg (by positivity)
      (mul_nonneg (by positivity) (div_nonneg hA0 hdelta.le))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hNearC : Mnear ≤ C := by dsimp only [C]; linarith
  have hLargeC : Clarge ≤ C := by dsimp only [C]; linarith
  have hFirstC : Cfirst ≤ C := by dsimp only [C]; linarith
  have hSecondC : Csecond ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro n u hu beta
  by_cases hbetaTop : beta = (⊤ : Param)
  · subst beta
    have ht := hlarge n A u le_rfl hu
    exact ⟨ht.2.2.2.2.1.trans hLargeC, ht.2.2.2.2.2.trans hLargeC⟩
  let alpha := ENNReal.toReal beta
  have hAlpha0 : 0 ≤ alpha := ENNReal.toReal_nonneg
  have hback : finiteParam alpha = beta := by
    simpa only [alpha, paramToReal] using finiteParam_paramToReal beta hbetaTop
  by_cases hAlphaZero : alpha = 0
  · have hbetaZero : beta = 0 := by simpa [hback] using congrArg finiteParam hAlphaZero
    rw [hbetaZero]
    simp [hC]
  have hAlphaPos : 0 < alpha := lt_of_le_of_ne hAlpha0 (Ne.symm hAlphaZero)
  by_cases hAlphaNear : alpha ∈ Icc (1 - delta) (1 + delta)
  · have hn := hnear n u hu alpha hAlphaNear
    have hnM : Cnear * (1 + Real.log (blockScale n)) *
        Real.rpow (blockScale n) (-eta) ≤ Mnear :=
      hMnear _ ⟨n, rfl⟩
    rw [← hback]
    constructor
    · exact (le_add_of_nonneg_right (abs_nonneg _)).trans hn |>.trans hnM |>.trans hNearC
    · exact (le_add_of_nonneg_left (abs_nonneg _)).trans hn |>.trans hnM |>.trans hNearC
  by_cases hAlphaLarge : A ≤ alpha
  · have ht := hlarge n alpha u hAlphaLarge hu
    rw [← hback]
    exact ⟨ht.2.2.1.trans hLargeC, ht.2.2.2.1.trans hLargeC⟩
  have hAlphaA : alpha ≤ A := le_of_not_ge hAlphaLarge
  have hAway : delta ≤ |alpha - 1| := by
    simp only [mem_Icc, not_and_or, not_le] at hAlphaNear
    rcases hAlphaNear with hleft | hright
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  have hm := finiteKernelCrudeBounds B n u U A delta alpha
    hU hu hAlphaPos hAlphaA hdelta hAway
  rw [← hback]
  exact ⟨hm.1.trans hFirstC, hm.2.trans hSecondC⟩

private theorem tendsto_rpow_blockScale_neg (eta : ℝ) (heta : 0 < eta) :
    Tendsto (fun n : ℕ => Real.rpow (blockScale n) (-eta))
      atTop (nhds 0) := by
  exact (tendsto_rpow_neg_atTop heta).comp tendsto_blockScale_atTop

private theorem dominantMomentAt {J : ℕ} (B : BlockData J)
    (alpha : ℝ) (k : Fin (J + 1))
    (hmax : ∀ j : Fin (J + 1), j ≠ k →
      blockExponent B j alpha < blockExponent B k alpha)
    (U : ℝ) (hU : 0 ≤ U) :
    ∃ eta C : ℝ, 0 < eta ∧ 0 ≤ C ∧
      (∀ (n : ℕ) (u : Fin (J + 1) → ℝ),
        (∀ j, |u j| ≤ U) →
          |blockEscortMean B n alpha u - u k| +
              |blockEscortSecond B n alpha u - (u k) ^ 2| +
              blockEscortVar B n alpha u ≤
            C * Real.rpow (blockScale n) (-eta)) ∧
      Tendsto (fun n : ℕ => C * Real.rpow (blockScale n) (-eta))
        atTop (nhds 0) := by
  let eta := pointExponentGap B k alpha
  have heta : 0 < eta := pointExponentGap_pos B k alpha hmax
  have hgap : ∀ a ∈ ({alpha} : Set ℝ), ∀ j : Fin (J + 1), j ≠ k →
      eta ≤ blockExponent B k a - blockExponent B j a := by
    intro a ha j hj
    simp only [mem_singleton_iff] at ha
    subst a
    exact pointExponentGap_le B k j alpha hj
  obtain ⟨C, hC, hbound⟩ :=
    (dominantBlock B ({alpha} : Set ℝ) k eta heta hgap).2 U hU
  refine ⟨eta, C, heta, hC, ?_, ?_⟩
  · intro n u hu
    exact (hbound u hu n alpha (mem_singleton alpha)).1
  · simpa only [mul_zero] using
      tendsto_const_nhds.mul (tendsto_rpow_blockScale_neg eta heta)

private theorem uniformPointError_tendsto_of_bound
    {E K : Type*} [Nonempty K]
    (fN : ℕ → E → K → ℝ) (f : E → K → ℝ) (e : E)
    (bound : ℕ → ℝ)
    (hBound : ∀ n k, |fN n e k - f e k| ≤ bound n)
    (hBoundTendsto : Tendsto bound atTop (nhds 0)) :
    Tendsto (fun n => uniformPointError fN f n e) atTop (nhds 0) := by
  have hpack : ∀ n, 0 ≤ uniformPointError fN f n e ∧
      uniformPointError fN f n e ≤ bound n := by
    intro n
    let S : Set ℝ := {r : ℝ | ∃ k : K, r = |fN n e k - f e k|}
    have hSNonempty : S.Nonempty := by
      obtain ⟨k⟩ := (inferInstance : Nonempty K)
      exact ⟨_, k, rfl⟩
    have hSBdd : BddAbove S := by
      refine ⟨bound n, ?_⟩
      rintro r ⟨k, rfl⟩
      exact hBound n k
    change 0 ≤ sSup S ∧ sSup S ≤ bound n
    constructor
    · obtain ⟨k⟩ := (inferInstance : Nonempty K)
      exact (abs_nonneg _).trans (le_csSup hSBdd ⟨k, rfl⟩)
    · exact csSup_le hSNonempty fun _ hr => by
        rcases hr with ⟨k, rfl⟩
        exact hBound n k
  apply squeeze_zero
  · exact fun n => (hpack n).1
  · exact fun n => (hpack n).2
  · exact hBoundTendsto

private theorem uniformPointError_bounds_of_bound
    {E K : Type*} [Nonempty K]
    (fN : ℕ → E → K → ℝ) (f : E → K → ℝ) (bound : ℝ)
    (hBound : ∀ n e k, |fN n e k - f e k| ≤ bound) :
    ∀ n e, 0 ≤ uniformPointError fN f n e ∧
      uniformPointError fN f n e ≤ bound := by
  intro n e
  let S : Set ℝ := {r : ℝ | ∃ k : K, r = |fN n e k - f e k|}
  have hSNonempty : S.Nonempty := by
    obtain ⟨k⟩ := (inferInstance : Nonempty K)
    exact ⟨_, k, rfl⟩
  have hSBdd : BddAbove S := by
    refine ⟨bound, ?_⟩
    rintro r ⟨k, rfl⟩
    exact hBound n e k
  change 0 ≤ sSup S ∧ sSup S ≤ bound
  constructor
  · obtain ⟨k⟩ := (inferInstance : Nonempty K)
    exact (abs_nonneg _).trans (le_csSup hSBdd ⟨k, rfl⟩)
  · exact csSup_le hSNonempty fun _ hr => by
      rcases hr with ⟨k, rfl⟩
      exact hBound n e k

private theorem measurable_uniformPointError_of_continuous
    {E K : Type*} [MeasurableSpace E] [TopologicalSpace K]
    [TopologicalSpace.SeparableSpace K]
    (fN : ℕ → E → K → ℝ) (f : E → K → ℝ) (n : ℕ)
    (hMeasN : ∀ u, Measurable (fun e => fN n e u))
    (hMeas : ∀ u, Measurable (fun e => f e u))
    (hCont : ∀ e, Continuous (fun u => |fN n e u - f e u|)) :
    Measurable (uniformPointError fN f n) := by
  have hSup : Measurable (fun e =>
      ⨆ u : K, ENNReal.ofReal |fN n e u - f e u|) := by
    have h := measurable_iSup_of_lowerSemicontinuous
      (f := fun u e => ENNReal.ofReal |fN n e u - f e u|)
      (fun u => by
        have hAbs : Measurable (fun e => |fN n e u - f e u|) := by
          simpa only [Pi.sub_apply, Real.norm_eq_abs] using
            ((hMeasN u).sub (hMeas u)).norm
        simpa only [Function.comp_def] using ENNReal.measurable_ofReal.comp hAbs)
      (fun e => (ENNReal.continuous_ofReal.comp (hCont e)).lowerSemicontinuous)
    have hEq : (fun e => ⨆ u : K, ENNReal.ofReal |fN n e u - f e u|) =
        (⨆ u : K, fun e => ENNReal.ofReal |fN n e u - f e u|) := by
      funext e
      exact (iSup_apply
        (f := fun u : K => fun e => ENNReal.ofReal |fN n e u - f e u|)
        (a := e)).symm
    rw [hEq]
    exact h
  have hEq : uniformPointError fN f n = fun e =>
      (⨆ u : K, ENNReal.ofReal |fN n e u - f e u|).toReal := by
    funext e
    unfold uniformPointError
    rw [show {r : ℝ | ∃ u : K, r = |fN n e u - f e u|} =
        Set.range (fun u : K => |fN n e u - f e u|) by
      ext r
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨u, rfl⟩
      · rintro ⟨u, rfl⟩
        exact ⟨u, rfl⟩,
      sSup_range, ENNReal.toReal_iSup (fun _ => ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal, abs_nonneg]
  rw [hEq]
  exact ENNReal.measurable_toReal.comp hSup

private theorem abs_limit_le_of_uniform_error
    {E K : Type*} [Nonempty K] [TopologicalSpace K] [CompactSpace K]
    (fN : ℕ → E → K → ℝ) (f : E → K → ℝ) (e : E) (C : ℝ)
    (hContN : ∀ n, Continuous (fun u => fN n e u))
    (hCont : Continuous (fun u => f e u))
    (hBound : ∀ n u, |fN n e u| ≤ C)
    (hConv : Tendsto (fun n => uniformPointError fN f n e) atTop (nhds 0)) :
    ∀ u, |f e u| ≤ C := by
  intro u
  have hBdd : ∀ n, BddAbove
      {r : ℝ | ∃ v : K, r = |fN n e v - f e v|} := by
    intro n
    rw [show {r : ℝ | ∃ v : K, r = |fN n e v - f e v|} =
        (fun v : K => |fN n e v - f e v|) '' Set.univ by
      ext r
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨v, mem_univ v, rfl⟩
      · rintro ⟨v, -, rfl⟩
        exact ⟨v, rfl⟩]
    exact isCompact_univ.bddAbove_image ((hContN n).sub hCont).abs.continuousOn
  have hPoint : ∀ n,
      |fN n e u - f e u| ≤ uniformPointError fN f n e := by
    intro n
    unfold uniformPointError
    exact le_csSup (hBdd n) ⟨u, rfl⟩
  have hDiff : Tendsto (fun n => |fN n e u - f e u|) atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun _ => abs_nonneg _
    · exact hPoint
    · exact hConv
  have hFn : Tendsto (fun n => fN n e u) atTop (nhds (f e u)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq] using hDiff
  have hAbs : Tendsto (fun n => |fN n e u|) atTop (nhds |f e u|) :=
    (continuous_abs.tendsto (f e u)).comp hFn
  exact le_of_tendsto hAbs (Eventually.of_forall fun n => hBound n u)

private theorem uniformBlockKernelErrors_tendsto_at {J : ℕ} (B : BlockData J)
    (T : Finset ℝ) (k : Param → Fin (J + 1)) (jTop : Fin (J + 1))
    (hOne : 1 ∉ T)
    (hkTop : k ⊤ = jTop)
    (hUnique : ∀ alpha : ℝ, 0 ≤ alpha → alpha ∉ T →
      ∀ j : Fin (J + 1), j ≠ k (finiteParam alpha) →
        blockExponent B j alpha <
          blockExponent B (k (finiteParam alpha)) alpha)
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop)
    (K : Set (Fin (J + 1) → ℝ)) [Nonempty K]
    (U : ℝ) (hU : 0 ≤ U) (hUK : ∀ u : K, ∀ j, |u.1 j| ≤ U)
    (beta : Param) (hBeta : beta ∉ T.image finiteParam) :
    Tendsto (fun n => uniformPointError
        (fun m beta (u : K) => blockKernelFirst B m u.1 beta)
        (fun beta (u : K) => blockLimitFirst k u.1 beta) n beta)
      atTop (nhds 0) ∧
    Tendsto (fun n => uniformPointError
        (fun m beta (u : K) => blockKernelSecond B m u.1 beta)
        (fun beta (u : K) => blockLimitSecond k u.1 beta) n beta)
      atTop (nhds 0) := by
  have hmax1 : ∀ j : Fin (J + 1), j ≠ k 1 →
      blockExponent B j 1 < blockExponent B (k 1) 1 := by
    intro j hj
    have hj' : j ≠ k (finiteParam 1) := by simpa only [finiteParam_one] using hj
    simpa only [finiteParam_one] using hUnique 1 zero_le_one hOne j hj'
  by_cases hbetaTop : beta = (⊤ : Param)
  · subst beta
    obtain ⟨eta, C, heta, hC, hmoment, hmomentTendsto⟩ :=
      dominantMomentAt B 1 (k 1) hmax1 U hU
    let b1 : ℕ → ℝ := fun n => C * Real.rpow (blockScale n) (-eta)
    let b2 : ℕ → ℝ := fun n => (2 * U) * b1 n
    have hb1 : ∀ n (u : K),
        |blockKernelFirst B n u.1 ⊤ - blockLimitFirst k u.1 ⊤| ≤ b1 n := by
      intro n u
      have hm := hmoment n u.1 (hUK u)
      have hmean : |blockEscortMean B n 1 u.1 - u.1 (k 1)| ≤ b1 n := by
        dsimp only [b1]
        linarith [abs_nonneg (blockEscortSecond B n 1 u.1 - (u.1 (k 1)) ^ 2),
          blockEscortVar_nonneg B n 1 u.1]
      rw [blockKernelFirst_top_eq B jTop hTop, blockLimitFirst,
        singularWeight_top, hkTop]
      change |(blockEscortMean B n 1 u.1 - u.1 jTop) -
        (-1 * (u.1 jTop - u.1 (k 1)))| ≤ b1 n
      rw [show (blockEscortMean B n 1 u.1 - u.1 jTop) -
        (-1 * (u.1 jTop - u.1 (k 1))) =
          blockEscortMean B n 1 u.1 - u.1 (k 1) by ring]
      exact hmean
    have hb2 : ∀ n (u : K),
        |blockKernelSecond B n u.1 ⊤ - blockLimitSecond k u.1 ⊤| ≤ b2 n := by
      intro n u
      have hm := hmoment n u.1 (hUK u)
      have hmean : |blockEscortMean B n 1 u.1 - u.1 (k 1)| ≤ b1 n := by
        dsimp only [b1]
        linarith [abs_nonneg (blockEscortSecond B n 1 u.1 - (u.1 (k 1)) ^ 2),
          blockEscortVar_nonneg B n 1 u.1]
      have hmeanBound := abs_blockEscortMean_le B n 1 u.1 U (hUK u)
      have hsq : |(u.1 (k 1)) ^ 2 - (blockEscortMean B n 1 u.1) ^ 2| ≤
          (2 * U) * |blockEscortMean B n 1 u.1 - u.1 (k 1)| := by
        rw [show (u.1 (k 1)) ^ 2 - (blockEscortMean B n 1 u.1) ^ 2 =
          (u.1 (k 1) - blockEscortMean B n 1 u.1) *
            (u.1 (k 1) + blockEscortMean B n 1 u.1) by ring, abs_mul,
          abs_sub_comm]
        calc
          |blockEscortMean B n 1 u.1 - u.1 (k 1)| *
              |u.1 (k 1) + blockEscortMean B n 1 u.1| ≤
              |blockEscortMean B n 1 u.1 - u.1 (k 1)| * (2 * U) :=
            mul_le_mul_of_nonneg_left (by
              calc
                |u.1 (k 1) + blockEscortMean B n 1 u.1| ≤
                    |u.1 (k 1)| + |blockEscortMean B n 1 u.1| := abs_add_le _ _
                _ ≤ U + U := add_le_add (hUK u (k 1)) hmeanBound
                _ = 2 * U := by ring) (abs_nonneg _)
          _ = (2 * U) * |blockEscortMean B n 1 u.1 - u.1 (k 1)| := by ring
      rw [blockKernelSecond_top_eq B jTop hTop, blockLimitSecond,
        singularWeight_top, hkTop]
      have heq :
          (u.1 jTop) ^ 2 - (blockEscortMean B n 1 u.1) ^ 2 -
              (-1 * ((u.1 (k 1)) ^ 2 - (u.1 jTop) ^ 2)) =
            (u.1 (k 1)) ^ 2 - (blockEscortMean B n 1 u.1) ^ 2 := by ring
      rw [heq]
      dsimp only [b2]
      exact hsq.trans (mul_le_mul_of_nonneg_left hmean (by positivity))
    refine ⟨uniformPointError_tendsto_of_bound _ _ ⊤ b1 hb1 hmomentTendsto,
      uniformPointError_tendsto_of_bound _ _ ⊤ b2 hb2 ?_⟩
    simpa only [b2, mul_zero] using tendsto_const_nhds.mul hmomentTendsto
  have hback := finiteParam_paramToReal beta hbetaTop
  let alpha := paramToReal beta hbetaTop
  have hAlpha0 : 0 ≤ alpha := by
    dsimp only [alpha, paramToReal]
    exact ENNReal.toReal_nonneg
  have hAlphaT : alpha ∉ T := by
    intro hmem
    apply hBeta
    exact Finset.mem_image.mpr ⟨alpha, hmem, hback⟩
  by_cases hAlphaZero : alpha = 0
  · have hbetaZero : beta = 0 := by
      dsimp only [alpha] at hAlphaZero
      rw [← hback, hAlphaZero, finiteParam_zero]
    rw [hbetaZero]
    constructor <;> simp [uniformPointError, blockLimitFirst, blockLimitSecond]
  have hAlphaPos : 0 < alpha := lt_of_le_of_ne hAlpha0 (Ne.symm hAlphaZero)
  by_cases hAlphaOne : alpha = 1
  · have hbetaOne : beta = 1 := by
      dsimp only [alpha] at hAlphaOne
      rw [← hback, hAlphaOne, finiteParam_one]
    rw [hbetaOne]
    obtain ⟨delta, eta, hdelta, hdeltaOne, heta, hnearGap, _⟩ :=
      nearOneDominance B T k hOne hUnique
    obtain ⟨C, hC, hbound, hboundTendsto⟩ :=
      nearShannonDominant B (k 1) delta eta U hdelta hdeltaOne heta hU hnearGap
    let q : ℕ → ℝ := fun n =>
      C * (1 + Real.log (blockScale n)) * Real.rpow (blockScale n) (-eta)
    have honeMem : (1 : ℝ) ∈ Icc (1 - delta) (1 + delta) := by
      constructor <;> linarith
    have hf : ∀ n (u : K),
        |blockKernelFirst B n u.1 1 - blockLimitFirst k u.1 1| ≤ q n := by
      intro n u
      have hb := hbound n u.1 (hUK u) 1 honeMem
      simpa only [finiteParam_one, blockLimitFirst_one, sub_zero, q] using
        (le_add_of_nonneg_right (abs_nonneg _)).trans hb
    have hs : ∀ n (u : K),
        |blockKernelSecond B n u.1 1 - blockLimitSecond k u.1 1| ≤ q n := by
      intro n u
      have hb := hbound n u.1 (hUK u) 1 honeMem
      simpa only [finiteParam_one, blockLimitSecond_one, sub_zero, q] using
        (le_add_of_nonneg_left (abs_nonneg _)).trans hb
    exact ⟨uniformPointError_tendsto_of_bound _ _ 1 q hf hboundTendsto,
      uniformPointError_tendsto_of_bound _ _ 1 q hs hboundTendsto⟩
  let ka := k beta
  have hmaxA : ∀ j : Fin (J + 1), j ≠ ka →
      blockExponent B j alpha < blockExponent B ka alpha := by
    intro j hj
    have h := hUnique alpha hAlpha0 hAlphaT j
    rw [hback] at h
    exact h hj
  obtain ⟨etaA, CA, hetaA, hCA, hmomentA, htendA⟩ :=
    dominantMomentAt B alpha ka hmaxA U hU
  obtain ⟨eta1, C1, heta1, hC1, hmoment1, htend1⟩ :=
    dominantMomentAt B 1 (k 1) hmax1 U hU
  let bA : ℕ → ℝ := fun n => CA * Real.rpow (blockScale n) (-etaA)
  let b1 : ℕ → ℝ := fun n => C1 * Real.rpow (blockScale n) (-eta1)
  let bf : ℕ → ℝ := fun n => |singularWeight beta| * (bA n + b1 n)
  let bs : ℕ → ℝ := fun n =>
    alpha * bA n + |singularWeight beta| * ((2 * U) * b1 n + (2 * U) * bA n)
  have hmeanA : ∀ n (u : K),
      |blockEscortMean B n alpha u.1 - u.1 ka| ≤ bA n := by
    intro n u
    have h := hmomentA n u.1 (hUK u)
    dsimp only [bA]
    linarith [abs_nonneg (blockEscortSecond B n alpha u.1 - (u.1 ka) ^ 2),
      blockEscortVar_nonneg B n alpha u.1]
  have hvarA : ∀ n (u : K), blockEscortVar B n alpha u.1 ≤ bA n := by
    intro n u
    have h := hmomentA n u.1 (hUK u)
    dsimp only [bA]
    linarith [abs_nonneg (blockEscortMean B n alpha u.1 - u.1 ka),
      abs_nonneg (blockEscortSecond B n alpha u.1 - (u.1 ka) ^ 2)]
  have hmean1 : ∀ n (u : K),
      |blockEscortMean B n 1 u.1 - u.1 (k 1)| ≤ b1 n := by
    intro n u
    have h := hmoment1 n u.1 (hUK u)
    dsimp only [b1]
    linarith [abs_nonneg (blockEscortSecond B n 1 u.1 - (u.1 (k 1)) ^ 2),
      blockEscortVar_nonneg B n 1 u.1]
  have hf : ∀ n (u : K),
      |blockKernelFirst B n u.1 beta - blockLimitFirst k u.1 beta| ≤ bf n := by
    intro n u
    have hma := hmeanA n u
    have hm1 := hmean1 n u
    have hback' : finiteParam alpha = beta := hback
    have hkAlpha : k (finiteParam alpha) = ka := by
      dsimp only [ka]
      exact congrArg k hback'
    rw [← hback, blockKernelFirst_finite B n u.1 hAlphaPos hAlphaOne,
      blockLimitFirst, hkAlpha]
    change |singularWeight (finiteParam alpha) *
        (blockEscortMean B n alpha u.1 - blockEscortMean B n 1 u.1) -
      singularWeight (finiteParam alpha) * (u.1 ka - u.1 (k 1))| ≤ bf n
    rw [← mul_sub, abs_mul]
    dsimp only [bf]
    rw [← hback]
    exact mul_le_mul_of_nonneg_left (by
      calc
        |(blockEscortMean B n alpha u.1 - blockEscortMean B n 1 u.1) -
            (u.1 ka - u.1 (k 1))| =
            |(blockEscortMean B n alpha u.1 - u.1 ka) -
              (blockEscortMean B n 1 u.1 - u.1 (k 1))| := by ring_nf
        _ ≤ |blockEscortMean B n alpha u.1 - u.1 ka| +
            |blockEscortMean B n 1 u.1 - u.1 (k 1)| := abs_sub _ _
        _ ≤ bA n + b1 n := add_le_add hma hm1) (abs_nonneg _)
  have hs : ∀ n (u : K),
      |blockKernelSecond B n u.1 beta - blockLimitSecond k u.1 beta| ≤ bs n := by
    intro n u
    have hma := hmeanA n u
    have hm1 := hmean1 n u
    have hva := hvarA n u
    have hMeanABound := abs_blockEscortMean_le B n alpha u.1 U (hUK u)
    have hMean1Bound := abs_blockEscortMean_le B n 1 u.1 U (hUK u)
    have hsqA : |(blockEscortMean B n alpha u.1) ^ 2 - (u.1 ka) ^ 2| ≤
        (2 * U) * |blockEscortMean B n alpha u.1 - u.1 ka| := by
      rw [show (blockEscortMean B n alpha u.1) ^ 2 - (u.1 ka) ^ 2 =
        (blockEscortMean B n alpha u.1 - u.1 ka) *
          (blockEscortMean B n alpha u.1 + u.1 ka) by ring, abs_mul]
      calc
        |blockEscortMean B n alpha u.1 - u.1 ka| *
            |blockEscortMean B n alpha u.1 + u.1 ka| ≤
            |blockEscortMean B n alpha u.1 - u.1 ka| * (2 * U) :=
          mul_le_mul_of_nonneg_left
            ((abs_add_le _ _).trans
              (by simpa only [two_mul] using add_le_add hMeanABound (hUK u ka)))
            (abs_nonneg _)
        _ = (2 * U) * |blockEscortMean B n alpha u.1 - u.1 ka| := by ring
    have hsq1 : |(blockEscortMean B n 1 u.1) ^ 2 - (u.1 (k 1)) ^ 2| ≤
        (2 * U) * |blockEscortMean B n 1 u.1 - u.1 (k 1)| := by
      rw [show (blockEscortMean B n 1 u.1) ^ 2 - (u.1 (k 1)) ^ 2 =
        (blockEscortMean B n 1 u.1 - u.1 (k 1)) *
          (blockEscortMean B n 1 u.1 + u.1 (k 1)) by ring, abs_mul]
      calc
        |blockEscortMean B n 1 u.1 - u.1 (k 1)| *
            |blockEscortMean B n 1 u.1 + u.1 (k 1)| ≤
            |blockEscortMean B n 1 u.1 - u.1 (k 1)| * (2 * U) :=
          mul_le_mul_of_nonneg_left
            ((abs_add_le _ _).trans
              (by simpa only [two_mul] using add_le_add hMean1Bound (hUK u (k 1))))
            (abs_nonneg _)
        _ = (2 * U) * |blockEscortMean B n 1 u.1 - u.1 (k 1)| := by ring
    have hback' : finiteParam alpha = beta := hback
    have hkAlpha : k (finiteParam alpha) = ka := by
      dsimp only [ka]
      exact congrArg k hback'
    rw [← hback, blockKernelSecond_finite B n u.1 hAlphaPos hAlphaOne,
      blockLimitSecond, hkAlpha]
    change |-alpha * blockEscortVar B n alpha u.1 +
        singularWeight (finiteParam alpha) *
          ((blockEscortMean B n 1 u.1) ^ 2 -
            (blockEscortMean B n alpha u.1) ^ 2) -
        singularWeight (finiteParam alpha) *
          ((u.1 (k 1)) ^ 2 - (u.1 ka) ^ 2)| ≤ bs n
    calc
      _ = |-alpha * blockEscortVar B n alpha u.1 +
          singularWeight (finiteParam alpha) *
            (((blockEscortMean B n 1 u.1) ^ 2 - (u.1 (k 1)) ^ 2) -
              ((blockEscortMean B n alpha u.1) ^ 2 - (u.1 ka) ^ 2))| := by
        congr 1
        ring
      _ ≤ alpha * blockEscortVar B n alpha u.1 +
          |singularWeight (finiteParam alpha)| *
            (|(blockEscortMean B n 1 u.1) ^ 2 - (u.1 (k 1)) ^ 2| +
              |(blockEscortMean B n alpha u.1) ^ 2 - (u.1 ka) ^ 2|) := by
        calc
          _ ≤ |-alpha * blockEscortVar B n alpha u.1| +
              |singularWeight (finiteParam alpha) *
                (((blockEscortMean B n 1 u.1) ^ 2 - (u.1 (k 1)) ^ 2) -
                  ((blockEscortMean B n alpha u.1) ^ 2 - (u.1 ka) ^ 2))| :=
            abs_add_le _ _
          _ ≤ _ := by
            rw [abs_mul, abs_neg, abs_of_pos hAlphaPos,
              abs_of_nonneg (blockEscortVar_nonneg B n alpha u.1), abs_mul]
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _))
      _ ≤ alpha * bA n + |singularWeight beta| *
          ((2 * U) * b1 n + (2 * U) * bA n) := by
        rw [← hback]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hva hAlpha0)
          (mul_le_mul_of_nonneg_left
            (add_le_add
              (hsq1.trans (mul_le_mul_of_nonneg_left hm1 (by positivity)))
              (hsqA.trans (mul_le_mul_of_nonneg_left hma (by positivity))))
            (abs_nonneg _))
      _ = bs n := rfl
  have hbf : Tendsto bf atTop (nhds 0) := by
    change Tendsto (fun n => |singularWeight beta| *
      (CA * Real.rpow (blockScale n) (-etaA) +
        C1 * Real.rpow (blockScale n) (-eta1))) atTop (nhds 0)
    have hc : Tendsto (fun _ : ℕ => |singularWeight beta|) atTop
        (nhds |singularWeight beta|) := tendsto_const_nhds
    simpa only [zero_add, mul_zero] using hc.mul (htendA.add htend1)
  have hbs : Tendsto bs atTop (nhds 0) := by
    dsimp only [bs]
    have halpha : Tendsto (fun _ : ℕ => alpha) atTop (nhds alpha) :=
      tendsto_const_nhds
    have htwoU : Tendsto (fun _ : ℕ => 2 * U) atTop (nhds (2 * U)) :=
      tendsto_const_nhds
    have hweight : Tendsto (fun _ : ℕ => |singularWeight beta|) atTop
        (nhds |singularWeight beta|) := tendsto_const_nhds
    have hleft : Tendsto
        (fun n => alpha * (CA * Real.rpow (blockScale n) (-etaA))) atTop
        (nhds 0) := by
      simpa only [mul_zero] using halpha.mul htendA
    have hrightInner : Tendsto
        (fun n => (2 * U) * (C1 * Real.rpow (blockScale n) (-eta1)) +
          (2 * U) * (CA * Real.rpow (blockScale n) (-etaA))) atTop
        (nhds 0) := by
      simpa only [mul_zero, add_zero] using (htwoU.mul htend1).add (htwoU.mul htendA)
    have hright : Tendsto
        (fun n => |singularWeight beta| *
          ((2 * U) * (C1 * Real.rpow (blockScale n) (-eta1)) +
            (2 * U) * (CA * Real.rpow (blockScale n) (-etaA)))) atTop
        (nhds 0) := by
      simpa only [mul_zero] using hweight.mul hrightInner
    simpa only [add_zero] using hleft.add hright
  exact ⟨uniformPointError_tendsto_of_bound _ _ beta bf hf hbf,
    uniformPointError_tendsto_of_bound _ _ beta bs hs hbs⟩

/-- Uniform passage from finite block kernels to their pointwise limit kernels
under a signed parameter measure (`prop:block-limit-passage`). -/
theorem blockLimitPassage {J : ℕ} (B : BlockData J)
    (mu : SignedMeasure Param) (T : Finset ℝ)
    (k : Param → Fin (J + 1)) (jTop : Fin (J + 1))
    (hOne : 1 ∉ T)
    (hAtoms : ∀ r ∈ T, signedTV mu ({finiteParam r} : Set Param) = 0)
    (hk : Measurable k) (hkTop : k ⊤ = jTop)
    (hUnique : ∀ alpha : ℝ, 0 ≤ alpha → alpha ∉ T →
      ∀ j : Fin (J + 1), j ≠ k (finiteParam alpha) →
        blockExponent B j alpha <
          blockExponent B (k (finiteParam alpha)) alpha)
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop)
    (K : Set (Fin (J + 1) → ℝ)) (hK : IsCompact K) (hK0 : K.Nonempty) :
    let UK := {u : Fin (J + 1) → ℝ // u ∈ K}
    letI : Nonempty UK := ⟨⟨hK0.choose, hK0.choose_spec⟩⟩
    letI : CompactSpace UK := isCompact_iff_compactSpace.mp hK
    (∀ (n : ℕ) (u : UK),
      Measurable (fun beta => blockKernelFirst B n u.1 beta) ∧
        Integrable (fun beta => blockKernelFirst B n u.1 beta) (signedTV mu)) ∧
    (∀ (n : ℕ) (u : UK),
      Measurable (fun beta => blockKernelSecond B n u.1 beta) ∧
        Integrable (fun beta => blockKernelSecond B n u.1 beta) (signedTV mu)) ∧
    (∀ u : UK,
      Measurable (fun beta => blockLimitFirst k u.1 beta) ∧
        Integrable (fun beta => blockLimitFirst k u.1 beta) (signedTV mu)) ∧
    (∀ u : UK,
      Measurable (fun beta => blockLimitSecond k u.1 beta) ∧
        Integrable (fun beta => blockLimitSecond k u.1 beta) (signedTV mu)) ∧
    Tendsto (fun n => uniformIntegralErrorSigned mu
      (fun m beta (u : UK) => blockKernelFirst B m u.1 beta)
      (fun beta (u : UK) => blockLimitFirst k u.1 beta) n)
      atTop (nhds 0) ∧
    Tendsto (fun n => uniformIntegralErrorSigned mu
      (fun m beta (u : UK) => blockKernelSecond B m u.1 beta)
      (fun beta (u : UK) => blockLimitSecond k u.1 beta) n)
      atTop (nhds 0) := by
  let UK := {u : Fin (J + 1) → ℝ // u ∈ K}
  letI : Nonempty UK := ⟨⟨hK0.choose, hK0.choose_spec⟩⟩
  letI : CompactSpace UK := isCompact_iff_compactSpace.mp hK
  obtain ⟨U, hU, hVelocity⟩ := exists_velocity_bound K hK hK0
  have hUK : ∀ (u : UK) (j : Fin (J + 1)), |u.1 j| ≤ U := by
    intro u j
    exact hVelocity u.1 u.2 j
  obtain ⟨C, hC, hKernelBound⟩ :=
    exists_uniform_blockKernel_bound B T k jTop hOne hUnique hTop U hU
  have hErrors : ∀ beta ∉ T.image finiteParam,
      Tendsto (fun n => uniformPointError
        (fun m beta (u : UK) => blockKernelFirst B m u.1 beta)
        (fun beta (u : UK) => blockLimitFirst k u.1 beta) n beta)
        atTop (nhds 0) ∧
      Tendsto (fun n => uniformPointError
        (fun m beta (u : UK) => blockKernelSecond B m u.1 beta)
        (fun beta (u : UK) => blockLimitSecond k u.1 beta) n beta)
        atTop (nhds 0) := by
    intro beta hbeta
    exact uniformBlockKernelErrors_tendsto_at B T k jTop hOne hkTop hUnique hTop
      K U hU hUK beta hbeta
  have hThresholdNull :
      signedTV mu (↑(T.image finiteParam) : Set Param) = 0 := by
    rw [← sum_measure_singleton]
    apply Finset.sum_eq_zero
    intro beta hbeta
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hbeta
    exact hAtoms r hr
  have hAEOutside : ∀ᵐ beta ∂signedTV mu,
      beta ∉ T.image finiteParam :=
    measure_eq_zero_iff_ae_notMem.mp hThresholdNull
  have hConvFirst : ∀ᵐ beta ∂signedTV mu,
      Tendsto (fun n => uniformPointError
        (fun m beta (u : UK) => blockKernelFirst B m u.1 beta)
        (fun beta (u : UK) => blockLimitFirst k u.1 beta) n beta)
        atTop (nhds 0) := by
    filter_upwards [hAEOutside] with beta hbeta
    exact (hErrors beta hbeta).1
  have hConvSecond : ∀ᵐ beta ∂signedTV mu,
      Tendsto (fun n => uniformPointError
        (fun m beta (u : UK) => blockKernelSecond B m u.1 beta)
        (fun beta (u : UK) => blockLimitSecond k u.1 beta) n beta)
        atTop (nhds 0) := by
    filter_upwards [hAEOutside] with beta hbeta
    exact (hErrors beta hbeta).2
  have hLimitFirstOutside : ∀ beta ∉ T.image finiteParam, ∀ u : UK,
      |blockLimitFirst k u.1 beta| ≤ C := by
    intro beta hbeta
    exact abs_limit_le_of_uniform_error
      (fun n beta (u : UK) => blockKernelFirst B n u.1 beta)
      (fun beta (u : UK) => blockLimitFirst k u.1 beta) beta C
      (fun n => (continuous_blockKernelFirst_velocity B jTop hTop n beta).comp
        continuous_subtype_val)
      ((continuous_blockLimitFirst_velocity k beta).comp continuous_subtype_val)
      (fun n u => (hKernelBound n u.1 (hUK u) beta).1)
      (hErrors beta hbeta).1
  have hLimitSecondOutside : ∀ beta ∉ T.image finiteParam, ∀ u : UK,
      |blockLimitSecond k u.1 beta| ≤ C := by
    intro beta hbeta
    exact abs_limit_le_of_uniform_error
      (fun n beta (u : UK) => blockKernelSecond B n u.1 beta)
      (fun beta (u : UK) => blockLimitSecond k u.1 beta) beta C
      (fun n => (continuous_blockKernelSecond_velocity B jTop hTop n beta).comp
        continuous_subtype_val)
      ((continuous_blockLimitSecond_velocity k beta).comp continuous_subtype_val)
      (fun n u => (hKernelBound n u.1 (hUK u) beta).2)
      (hErrors beta hbeta).2
  let WT : ℝ := ∑ r ∈ T, |singularWeight (finiteParam r)|
  have hWT : 0 ≤ WT := by
    dsimp only [WT]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hThresholdWeight : ∀ beta ∈ T.image finiteParam,
      |singularWeight beta| ≤ WT := by
    intro beta hbeta
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hbeta
    dsimp only [WT]
    exact Finset.single_le_sum (fun s _ => abs_nonneg (singularWeight (finiteParam s))) hr
  have hLimitFirstThreshold : ∀ beta ∈ T.image finiteParam, ∀ u : UK,
      |blockLimitFirst k u.1 beta| ≤ 2 * U * WT := by
    intro beta hbeta u
    have hDiff : |u.1 (k beta) - u.1 (k 1)| ≤ 2 * U := by
      calc
        |u.1 (k beta) - u.1 (k 1)| ≤
            |u.1 (k beta)| + |u.1 (k 1)| := abs_sub _ _
        _ ≤ U + U := add_le_add (hUK u (k beta)) (hUK u (k 1))
        _ = 2 * U := by ring
    rw [blockLimitFirst, abs_mul]
    calc
      |singularWeight beta| * |u.1 (k beta) - u.1 (k 1)| ≤
          WT * (2 * U) :=
        mul_le_mul (hThresholdWeight beta hbeta) hDiff (abs_nonneg _) hWT
      _ = 2 * U * WT := by ring
  have hLimitSecondThreshold : ∀ beta ∈ T.image finiteParam, ∀ u : UK,
      |blockLimitSecond k u.1 beta| ≤ 2 * U ^ 2 * WT := by
    intro beta hbeta u
    have hSq : ∀ j : Fin (J + 1), |(u.1 j) ^ 2| ≤ U ^ 2 := by
      intro j
      rw [abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq.mpr (by
        simpa only [abs_of_nonneg hU] using hUK u j)
    have hDiff : |(u.1 (k 1)) ^ 2 - (u.1 (k beta)) ^ 2| ≤ 2 * U ^ 2 := by
      calc
        |(u.1 (k 1)) ^ 2 - (u.1 (k beta)) ^ 2| ≤
            |(u.1 (k 1)) ^ 2| + |(u.1 (k beta)) ^ 2| := abs_sub _ _
        _ ≤ U ^ 2 + U ^ 2 := add_le_add (hSq (k 1)) (hSq (k beta))
        _ = 2 * U ^ 2 := by ring
    rw [blockLimitSecond, abs_mul]
    calc
      |singularWeight beta| *
          |(u.1 (k 1)) ^ 2 - (u.1 (k beta)) ^ 2| ≤
          WT * (2 * U ^ 2) :=
        mul_le_mul (hThresholdWeight beta hbeta) hDiff (abs_nonneg _) hWT
      _ = 2 * U ^ 2 * WT := by ring
  let L1 := C + 2 * U * WT
  let L2 := C + 2 * U ^ 2 * WT
  have hL1 : 0 ≤ L1 := by dsimp only [L1]; positivity
  have hL2 : 0 ≤ L2 := by dsimp only [L2]; positivity
  have hLimitFirstBound : ∀ beta (u : UK),
      |blockLimitFirst k u.1 beta| ≤ L1 := by
    intro beta u
    by_cases hbeta : beta ∈ T.image finiteParam
    · exact (hLimitFirstThreshold beta hbeta u).trans (by
        dsimp only [L1]
        linarith)
    · exact (hLimitFirstOutside beta hbeta u).trans (by
        dsimp only [L1]
        exact le_add_of_nonneg_right (by positivity))
  have hLimitSecondBound : ∀ beta (u : UK),
      |blockLimitSecond k u.1 beta| ≤ L2 := by
    intro beta u
    by_cases hbeta : beta ∈ T.image finiteParam
    · exact (hLimitSecondThreshold beta hbeta u).trans (by
        dsimp only [L2]
        linarith)
    · exact (hLimitSecondOutside beta hbeta u).trans (by
        dsimp only [L2]
        exact le_add_of_nonneg_right (by positivity))
  have hKernelFirstTV : ∀ (n : ℕ) (u : UK),
      Measurable (fun beta => blockKernelFirst B n u.1 beta) ∧
        Integrable (fun beta => blockKernelFirst B n u.1 beta) (signedTV mu) := by
    intro n u
    refine ⟨measurable_blockKernelFirst B jTop hTop n u.1, ?_⟩
    apply (integrable_const C).mono
      (measurable_blockKernelFirst B jTop hTop n u.1).aestronglyMeasurable
    filter_upwards [] with beta
    simpa only [Real.norm_eq_abs, abs_of_nonneg hC] using
      (hKernelBound n u.1 (hUK u) beta).1
  have hKernelSecondTV : ∀ (n : ℕ) (u : UK),
      Measurable (fun beta => blockKernelSecond B n u.1 beta) ∧
        Integrable (fun beta => blockKernelSecond B n u.1 beta) (signedTV mu) := by
    intro n u
    refine ⟨measurable_blockKernelSecond B jTop hTop n u.1, ?_⟩
    apply (integrable_const C).mono
      (measurable_blockKernelSecond B jTop hTop n u.1).aestronglyMeasurable
    filter_upwards [] with beta
    simpa only [Real.norm_eq_abs, abs_of_nonneg hC] using
      (hKernelBound n u.1 (hUK u) beta).2
  have hLimitFirstTV : ∀ u : UK,
      Measurable (fun beta => blockLimitFirst k u.1 beta) ∧
        Integrable (fun beta => blockLimitFirst k u.1 beta) (signedTV mu) := by
    intro u
    refine ⟨measurable_blockLimitFirst hk u.1, ?_⟩
    apply (integrable_const L1).mono
      (measurable_blockLimitFirst hk u.1).aestronglyMeasurable
    filter_upwards [] with beta
    simpa only [Real.norm_eq_abs, abs_of_nonneg hL1] using hLimitFirstBound beta u
  have hLimitSecondTV : ∀ u : UK,
      Measurable (fun beta => blockLimitSecond k u.1 beta) ∧
        Integrable (fun beta => blockLimitSecond k u.1 beta) (signedTV mu) := by
    intro u
    refine ⟨measurable_blockLimitSecond hk u.1, ?_⟩
    apply (integrable_const L2).mono
      (measurable_blockLimitSecond hk u.1).aestronglyMeasurable
    filter_upwards [] with beta
    simpa only [Real.norm_eq_abs, abs_of_nonneg hL2] using hLimitSecondBound beta u
  let G1 := C + L1
  let G2 := C + L2
  have hErrorFirst : ∀ n beta (u : UK),
      |blockKernelFirst B n u.1 beta - blockLimitFirst k u.1 beta| ≤ G1 := by
    intro n beta u
    calc
      |blockKernelFirst B n u.1 beta - blockLimitFirst k u.1 beta| ≤
          |blockKernelFirst B n u.1 beta| + |blockLimitFirst k u.1 beta| :=
        abs_sub _ _
      _ ≤ C + L1 := add_le_add
        (hKernelBound n u.1 (hUK u) beta).1 (hLimitFirstBound beta u)
      _ = G1 := rfl
  have hErrorSecond : ∀ n beta (u : UK),
      |blockKernelSecond B n u.1 beta - blockLimitSecond k u.1 beta| ≤ G2 := by
    intro n beta u
    calc
      |blockKernelSecond B n u.1 beta - blockLimitSecond k u.1 beta| ≤
          |blockKernelSecond B n u.1 beta| + |blockLimitSecond k u.1 beta| :=
        abs_sub _ _
      _ ≤ C + L2 := add_le_add
        (hKernelBound n u.1 (hUK u) beta).2 (hLimitSecondBound beta u)
      _ = G2 := rfl
  have hPointFirst := uniformPointError_bounds_of_bound
    (fun n beta (u : UK) => blockKernelFirst B n u.1 beta)
    (fun beta (u : UK) => blockLimitFirst k u.1 beta) G1 hErrorFirst
  have hPointSecond := uniformPointError_bounds_of_bound
    (fun n beta (u : UK) => blockKernelSecond B n u.1 beta)
    (fun beta (u : UK) => blockLimitSecond k u.1 beta) G2 hErrorSecond
  have hPointMeasFirst : ∀ n, Measurable (uniformPointError
      (fun m beta (u : UK) => blockKernelFirst B m u.1 beta)
      (fun beta (u : UK) => blockLimitFirst k u.1 beta) n) := by
    intro n
    apply measurable_uniformPointError_of_continuous
    · exact fun u => measurable_blockKernelFirst B jTop hTop n u.1
    · exact fun u => measurable_blockLimitFirst hk u.1
    · intro beta
      exact (((continuous_blockKernelFirst_velocity B jTop hTop n beta).sub
        (continuous_blockLimitFirst_velocity k beta)).abs).comp continuous_subtype_val
  have hPointMeasSecond : ∀ n, Measurable (uniformPointError
      (fun m beta (u : UK) => blockKernelSecond B m u.1 beta)
      (fun beta (u : UK) => blockLimitSecond k u.1 beta) n) := by
    intro n
    apply measurable_uniformPointError_of_continuous
    · exact fun u => measurable_blockKernelSecond B jTop hTop n u.1
    · exact fun u => measurable_blockLimitSecond hk u.1
    · intro beta
      exact (((continuous_blockKernelSecond_velocity B jTop hTop n beta).sub
        (continuous_blockLimitSecond_velocity k beta)).abs).comp continuous_subtype_val
  have hBddFirst : ∀ n beta, BddAbove
      {r : ℝ | ∃ u : UK, r =
        |blockKernelFirst B n u.1 beta - blockLimitFirst k u.1 beta|} := by
    intro n beta
    exact ⟨G1, by rintro r ⟨u, rfl⟩; exact hErrorFirst n beta u⟩
  have hBddSecond : ∀ n beta, BddAbove
      {r : ℝ | ∃ u : UK, r =
        |blockKernelSecond B n u.1 beta - blockLimitSecond k u.1 beta|} := by
    intro n beta
    exact ⟨G2, by rintro r ⟨u, rfl⟩; exact hErrorSecond n beta u⟩
  have hKernelFirstParts : ∀ (n : ℕ) (u : UK),
      Measurable (fun beta => blockKernelFirst B n u.1 beta) ∧
      Integrable (fun beta => blockKernelFirst B n u.1 beta) (signedPos mu) ∧
      Integrable (fun beta => blockKernelFirst B n u.1 beta) (signedNeg mu) := by
    intro n u
    have hInt := (hKernelFirstTV n u).2
    rw [signedTV_eq_add] at hInt
    exact ⟨(hKernelFirstTV n u).1, hInt.left_of_add_measure,
      hInt.right_of_add_measure⟩
  have hKernelSecondParts : ∀ (n : ℕ) (u : UK),
      Measurable (fun beta => blockKernelSecond B n u.1 beta) ∧
      Integrable (fun beta => blockKernelSecond B n u.1 beta) (signedPos mu) ∧
      Integrable (fun beta => blockKernelSecond B n u.1 beta) (signedNeg mu) := by
    intro n u
    have hInt := (hKernelSecondTV n u).2
    rw [signedTV_eq_add] at hInt
    exact ⟨(hKernelSecondTV n u).1, hInt.left_of_add_measure,
      hInt.right_of_add_measure⟩
  have hLimitFirstParts : ∀ u : UK,
      Measurable (fun beta => blockLimitFirst k u.1 beta) ∧
      Integrable (fun beta => blockLimitFirst k u.1 beta) (signedPos mu) ∧
      Integrable (fun beta => blockLimitFirst k u.1 beta) (signedNeg mu) := by
    intro u
    have hInt := (hLimitFirstTV u).2
    rw [signedTV_eq_add] at hInt
    exact ⟨(hLimitFirstTV u).1, hInt.left_of_add_measure,
      hInt.right_of_add_measure⟩
  have hLimitSecondParts : ∀ u : UK,
      Measurable (fun beta => blockLimitSecond k u.1 beta) ∧
      Integrable (fun beta => blockLimitSecond k u.1 beta) (signedPos mu) ∧
      Integrable (fun beta => blockLimitSecond k u.1 beta) (signedNeg mu) := by
    intro u
    have hInt := (hLimitSecondTV u).2
    rw [signedTV_eq_add] at hInt
    exact ⟨(hLimitSecondTV u).1, hInt.left_of_add_measure,
      hInt.right_of_add_measure⟩
  have hDCTFirst := uniformDCTSigned mu
    (fun n beta (u : UK) => blockKernelFirst B n u.1 beta)
    (fun beta (u : UK) => blockLimitFirst k u.1 beta)
    (fun _ : Param => G1) hKernelFirstParts hLimitFirstParts hBddFirst
    hPointMeasFirst hConvFirst (integrable_const G1) hPointFirst
  have hDCTSecond := uniformDCTSigned mu
    (fun n beta (u : UK) => blockKernelSecond B n u.1 beta)
    (fun beta (u : UK) => blockLimitSecond k u.1 beta)
    (fun _ : Param => G2) hKernelSecondParts hLimitSecondParts hBddSecond
    hPointMeasSecond hConvSecond (integrable_const G2) hPointSecond
  exact ⟨hKernelFirstTV, hKernelSecondTV, hLimitFirstTV, hLimitSecondTV,
    hDCTFirst.2, hDCTSecond.2⟩

end ConditionalEntropy
