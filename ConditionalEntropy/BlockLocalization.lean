import ConditionalEntropy.BlockCurves
import ConditionalEntropy.BlockLimitPassage
import ConditionalEntropy.BlockLimitPolynomials

/-!
# Two- and three-block localization

This module evaluates the block-limit integrals and transports the uniform
block-limit passage to the logarithmic and norm-free scalar curves used by
the localization arguments.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

theorem integrable_singularWeight_Iio
    (nu : Measure Param) [IsFiniteMeasure nu] {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    Integrable ((Iio (finiteParam r)).indicator singularWeight) nu := by
  let C := r / (1 - r)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  apply (integrable_const C).mono
    (measurable_singularWeight.indicator measurableSet_Iio).aestronglyMeasurable
  filter_upwards [] with beta
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hC]
  by_cases hbeta : beta ∈ Iio (finiteParam r)
  · rw [Set.indicator_of_mem hbeta]
    have hbetaTop : beta ≠ ⊤ := by
      exact ne_of_lt (hbeta.trans (lt_top_iff_ne_top.mpr (finiteParam_ne_top r)))
    let x := ENNReal.toReal beta
    have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
    have hxr : x < r := by
      dsimp only [x]
      exact ENNReal.toReal_lt_of_lt_ofReal hbeta
    have hx1 : x ≠ 1 := by linarith
    have hback : finiteParam x = beta := by
      simpa only [x, paramToReal] using finiteParam_paramToReal beta hbetaTop
    rw [← hback, singularWeight_finite hx0 hx1, abs_div,
      abs_of_nonneg hx0, abs_of_pos (by linarith : 0 < 1 - x)]
    dsimp only [C]
    exact (div_le_div_iff₀ (by linarith : 0 < 1 - x)
      (by linarith : 0 < 1 - r)).mpr (by nlinarith)
  · rw [Set.indicator_of_notMem hbeta, abs_zero]
    exact hC

theorem integrable_singularWeight_Ioi
    (nu : Measure Param) [IsFiniteMeasure nu] {r : ℝ}
    (hr1 : 1 < r) :
    Integrable ((Ioi (finiteParam r)).indicator singularWeight) nu := by
  let C := r / (r - 1)
  have hr : 0 < r := lt_trans zero_lt_one hr1
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  apply (integrable_const C).mono
    (measurable_singularWeight.indicator measurableSet_Ioi).aestronglyMeasurable
  filter_upwards [] with beta
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hC]
  by_cases hbeta : beta ∈ Ioi (finiteParam r)
  · rw [Set.indicator_of_mem hbeta]
    by_cases hbetaTop : beta = ⊤
    · subst beta
      rw [singularWeight_top, abs_neg, abs_one]
      dsimp only [C]
      exact (le_div_iff₀ (by linarith : 0 < r - 1)).mpr (by linarith)
    · let x := ENNReal.toReal beta
      have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
      have hrx : r < x := by
        dsimp only [x]
        exact (ENNReal.ofReal_lt_iff_lt_toReal hr.le hbetaTop).mp hbeta
      have hx1 : x ≠ 1 := by linarith
      have hback : finiteParam x = beta := by
        simpa only [x, paramToReal] using finiteParam_paramToReal beta hbetaTop
      rw [← hback, singularWeight_finite hx0 hx1, abs_div,
        abs_of_nonneg hx0, abs_of_neg (by linarith : 1 - x < 0), neg_sub]
      dsimp only [C]
      exact (div_le_div_iff₀ (by linarith : 0 < x - 1)
        (by linarith : 0 < r - 1)).mpr (by nlinarith)
  · rw [Set.indicator_of_notMem hbeta, abs_zero]
    exact hC

theorem integrable_singularWeight_Ioo_of_lt
    (nu : Measure Param) [IsFiniteMeasure nu] {a b : ℝ}
    (hb : 0 < b) (hb1 : b < 1) :
    Integrable ((Ioo (finiteParam a) (finiteParam b)).indicator singularWeight) nu := by
  apply (integrable_singularWeight_Iio nu hb hb1).mono
    (measurable_singularWeight.indicator measurableSet_Ioo).aestronglyMeasurable
  filter_upwards [] with beta
  by_cases hbeta : beta ∈ Ioo (finiteParam a) (finiteParam b)
  · rw [Set.indicator_of_mem hbeta]
    rw [Set.indicator_of_mem (show beta ∈ Iio (finiteParam b) from hbeta.2)]
  · rw [Set.indicator_of_notMem hbeta]
    simp

theorem integrable_singularWeight_Ioo_of_gt
    (nu : Measure Param) [IsFiniteMeasure nu] {a b : ℝ}
    (ha1 : 1 < a) :
    Integrable ((Ioo (finiteParam a) (finiteParam b)).indicator singularWeight) nu := by
  apply (integrable_singularWeight_Ioi nu ha1).mono
    (measurable_singularWeight.indicator measurableSet_Ioo).aestronglyMeasurable
  filter_upwards [] with beta
  by_cases hbeta : beta ∈ Ioo (finiteParam a) (finiteParam b)
  · rw [Set.indicator_of_mem hbeta]
    rw [Set.indicator_of_mem (show beta ∈ Ioi (finiteParam a) from hbeta.1)]
  · rw [Set.indicator_of_notMem hbeta]
    simp

private theorem twoDominanceMap_one_of_lt {r : ℝ} (hr : 0 < r)
    (h : 1 < r) : twoDominanceMap r 1 = 0 := by
  unfold twoDominanceMap
  rw [if_pos]
  rw [← finiteParam_one]
  change ENNReal.ofReal 1 < ENNReal.ofReal r
  exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr h

private theorem twoDominanceMap_one_of_gt {r : ℝ}
    (h : r < 1) : twoDominanceMap r 1 = 1 := by
  unfold twoDominanceMap
  rw [if_neg]
  rw [← finiteParam_one]
  exact not_lt.mpr (ENNReal.ofReal_le_ofReal h.le)

private def threeCellWeight (a b : ℝ) : Fin 3 → Param → ℝ :=
  ![(Iio (finiteParam a)).indicator singularWeight,
    (Ioo (finiteParam a) (finiteParam b)).indicator singularWeight,
    (Ioi (finiteParam b)).indicator singularWeight]

@[simp] private theorem signedIntegral_threeCellWeight
    (mu : SignedMeasure Param) (a b : ℝ) (j : Fin 3) :
    signedIntegral mu (threeCellWeight a b j) = threeCellMoment mu a b j := by
  fin_cases j <;> rfl

private theorem integrable_threeCellWeight_off_norm
    (nu : Measure Param) [IsFiniteMeasure nu]
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (j : Fin 3) (hj : j ≠ threeNormBlock a b) :
    Integrable (threeCellWeight a b j) nu := by
  have hb : 0 < b := ha.trans hab
  by_cases h1a : 1 < a
  · fin_cases j
    · simp [threeNormBlock, h1a] at hj
    · simpa [threeCellWeight] using
        integrable_singularWeight_Ioo_of_gt nu (a := a) (b := b) h1a
    · simpa [threeCellWeight] using
        integrable_singularWeight_Ioi nu (r := b) (h1a.trans hab)
  · have haLt : a < 1 := lt_of_le_of_ne (not_lt.mp h1a) ha1
    by_cases h1b : 1 < b
    · fin_cases j
      · simpa [threeCellWeight] using
          integrable_singularWeight_Iio nu ha haLt
      · simp [threeNormBlock, h1a, h1b] at hj
      · simpa [threeCellWeight] using
          integrable_singularWeight_Ioi nu h1b
    · have hbLt : b < 1 := lt_of_le_of_ne (not_lt.mp h1b) hb1
      fin_cases j
      · simpa [threeCellWeight] using
          integrable_singularWeight_Iio nu ha haLt
      · simpa [threeCellWeight] using
          integrable_singularWeight_Ioo_of_lt nu hb hbLt
      · simp [threeNormBlock, h1a, h1b] at hj

private theorem threeDominanceMap_one_eq_normBlock
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    threeDominanceMap a b 1 = threeNormBlock a b := by
  have hb : 0 < b := ha.trans hab
  have hcmpA : finiteParam 1 < finiteParam a ↔ 1 < a := by
    change ENNReal.ofReal 1 < ENNReal.ofReal a ↔ 1 < a
    exact ENNReal.ofReal_lt_ofReal_iff ha
  have hcmpB : finiteParam 1 < finiteParam b ↔ 1 < b := by
    change ENNReal.ofReal 1 < ENNReal.ofReal b ↔ 1 < b
    exact ENNReal.ofReal_lt_ofReal_iff hb
  rw [← finiteParam_one]
  simp only [threeDominanceMap, threeNormBlock, hcmpA, hcmpB]

private theorem blockLimitFirst_three_eq_sum
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (u : Fin 3 → ℝ)
    (beta : Param) (hA : beta ≠ finiteParam a)
    (hB : beta ≠ finiteParam b) :
    blockLimitFirst (threeDominanceMap a b) u beta =
      ∑ j ∈ Finset.univ.erase (threeNormBlock a b),
        (u j - u (threeNormBlock a b)) * threeCellWeight a b j beta := by
  have hb : 0 < b := ha.trans hab
  have hAB : finiteParam a < finiteParam b := by
    change ENNReal.ofReal a < ENNReal.ofReal b
    exact (ENNReal.ofReal_lt_ofReal_iff hb).mpr hab
  have hk1 := threeDominanceMap_one_eq_normBlock a b ha hab
  by_cases hbetaA : beta < finiteParam a
  · have hmap : threeDominanceMap a b beta = 0 := by
      simp [threeDominanceMap, hbetaA]
    have hnotA : ¬finiteParam a < beta := not_lt.mpr hbetaA.le
    have hnotB : ¬finiteParam b < beta :=
      not_lt.mpr (hbetaA.le.trans hAB.le)
    rw [blockLimitFirst, hmap, hk1]
    by_cases h1a : 1 < a
    · simp [threeNormBlock, h1a, threeCellWeight, hbetaA, hnotA, hnotB,
        Fin.sum_univ_three]
    · by_cases h1b : 1 < b <;>
        simp [threeNormBlock, h1a, h1b, threeCellWeight, hbetaA, hnotA, hnotB,
          Fin.sum_univ_three] <;>
        ring
  · have hAbeta : finiteParam a < beta :=
      lt_of_le_of_ne (not_lt.mp hbetaA) hA.symm
    by_cases hbetaB : beta < finiteParam b
    · have hmap : threeDominanceMap a b beta = 1 := by
        simp [threeDominanceMap, hbetaA, hbetaB]
      have hnotB : ¬finiteParam b < beta := not_lt.mpr hbetaB.le
      rw [blockLimitFirst, hmap, hk1]
      by_cases h1a : 1 < a
      · simp [threeNormBlock, h1a, threeCellWeight, hbetaA, hAbeta, hbetaB, hnotB,
          Fin.sum_univ_three]
        ring
      · by_cases h1b : 1 < b
        · simp [threeNormBlock, h1a, h1b, threeCellWeight, hbetaA, hAbeta,
            hbetaB, hnotB, Fin.sum_univ_three]
        · simp [threeNormBlock, h1a, h1b, threeCellWeight, hbetaA, hAbeta,
            hbetaB, hnotB, Fin.sum_univ_three]
          ring
    · have hBbeta : finiteParam b < beta :=
        lt_of_le_of_ne (not_lt.mp hbetaB) hB.symm
      have hmap : threeDominanceMap a b beta = 2 := by
        simp [threeDominanceMap, hbetaA, hbetaB]
      have hnotIoo : ¬beta ∈ Ioo (finiteParam a) (finiteParam b) := by
        exact fun h => (not_lt.mpr hBbeta.le) h.2
      rw [blockLimitFirst, hmap, hk1]
      by_cases h1a : 1 < a
      · simp [threeNormBlock, h1a, threeCellWeight, hbetaA, hBbeta, hnotIoo,
          Fin.sum_univ_three]
        ring
      · by_cases h1b : 1 < b
        · simp [threeNormBlock, h1a, h1b, threeCellWeight, hbetaA,
            hBbeta, hnotIoo, Fin.sum_univ_three]
          ring
        · simp [threeNormBlock, h1a, h1b, threeCellWeight, hbetaA,
            hBbeta, hnotIoo, Fin.sum_univ_three]

private theorem blockLimitSecond_three_eq_sum
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (u : Fin 3 → ℝ)
    (beta : Param) (hA : beta ≠ finiteParam a)
    (hB : beta ≠ finiteParam b) :
    blockLimitSecond (threeDominanceMap a b) u beta =
      ∑ j ∈ Finset.univ.erase (threeNormBlock a b),
        ((u (threeNormBlock a b)) ^ 2 - (u j) ^ 2) *
          threeCellWeight a b j beta := by
  have hb : 0 < b := ha.trans hab
  have hAB : finiteParam a < finiteParam b := by
    change ENNReal.ofReal a < ENNReal.ofReal b
    exact (ENNReal.ofReal_lt_ofReal_iff hb).mpr hab
  have hk1 := threeDominanceMap_one_eq_normBlock a b ha hab
  by_cases hbetaA : beta < finiteParam a
  · have hmap : threeDominanceMap a b beta = 0 := by
      simp [threeDominanceMap, hbetaA]
    have hnotA : ¬finiteParam a < beta := not_lt.mpr hbetaA.le
    have hnotB : ¬finiteParam b < beta :=
      not_lt.mpr (hbetaA.le.trans hAB.le)
    rw [blockLimitSecond, hmap, hk1]
    by_cases h1a : 1 < a
    · simp [threeNormBlock, h1a, threeCellWeight, hbetaA, hnotA, hnotB,
        Fin.sum_univ_three]
    · by_cases h1b : 1 < b <;>
        simp [threeNormBlock, h1a, h1b, threeCellWeight, hbetaA, hnotA, hnotB,
          Fin.sum_univ_three] <;>
        ring
  · have hAbeta : finiteParam a < beta :=
      lt_of_le_of_ne (not_lt.mp hbetaA) hA.symm
    by_cases hbetaB : beta < finiteParam b
    · have hmap : threeDominanceMap a b beta = 1 := by
        simp [threeDominanceMap, hbetaA, hbetaB]
      have hnotB : ¬finiteParam b < beta := not_lt.mpr hbetaB.le
      rw [blockLimitSecond, hmap, hk1]
      by_cases h1a : 1 < a
      · simp [threeNormBlock, h1a, threeCellWeight, hbetaA, hAbeta, hbetaB, hnotB,
          Fin.sum_univ_three]
        ring
      · by_cases h1b : 1 < b
        · simp [threeNormBlock, h1a, h1b, threeCellWeight, hbetaA, hAbeta,
            hbetaB, hnotB, Fin.sum_univ_three]
        · simp [threeNormBlock, h1a, h1b, threeCellWeight, hbetaA, hAbeta,
            hbetaB, hnotB, Fin.sum_univ_three]
          ring
    · have hBbeta : finiteParam b < beta :=
        lt_of_le_of_ne (not_lt.mp hbetaB) hB.symm
      have hmap : threeDominanceMap a b beta = 2 := by
        simp [threeDominanceMap, hbetaA, hbetaB]
      have hnotIoo : ¬beta ∈ Ioo (finiteParam a) (finiteParam b) := by
        exact fun h => (not_lt.mpr hBbeta.le) h.2
      rw [blockLimitSecond, hmap, hk1]
      by_cases h1a : 1 < a
      · simp [threeNormBlock, h1a, threeCellWeight, hbetaA, hBbeta, hnotIoo,
          Fin.sum_univ_three]
        ring
      · by_cases h1b : 1 < b
        · simp [threeNormBlock, h1a, h1b, threeCellWeight, hbetaA,
            hBbeta, hnotIoo, Fin.sum_univ_three]
          ring
        · simp [threeNormBlock, h1a, h1b, threeCellWeight, hbetaA,
            hBbeta, hnotIoo, Fin.sum_univ_three]

/-- Evaluation of the two-block pointwise limit kernels against the signed
parameter measure (`lem:two-block-limit-integral-eval`). -/
theorem twoBlockLimitIntegralEval (mu : SignedMeasure Param) (r : ℝ)
    (hr : 0 < r) (u : Fin 2 → ℝ)
    (hmu : signedTV mu ({finiteParam r} : Set Param) = 0) :
    (1 < r →
      signedIntegral mu (fun beta => blockLimitFirst (twoDominanceMap r) u beta) =
          twoUpperGFirst mu r u ∧
        signedIntegral mu (fun beta => blockLimitSecond (twoDominanceMap r) u beta) =
          twoUpperGSecond mu r u) ∧
    (r < 1 →
      signedIntegral mu (fun beta => blockLimitFirst (twoDominanceMap r) u beta) =
          twoLowerGFirst mu r u ∧
        signedIntegral mu (fun beta => blockLimitSecond (twoDominanceMap r) u beta) =
          twoLowerGSecond mu r u) := by
  have hAE : ∀ᵐ beta ∂signedTV mu, beta ≠ finiteParam r := by
    simpa only [mem_singleton_iff, not_false_eq_true] using
      (measure_eq_zero_iff_ae_notMem.mp hmu)
  constructor
  · intro h1r
    have hk1 := twoDominanceMap_one_of_lt hr h1r
    have hFirstAE : (fun beta => blockLimitFirst (twoDominanceMap r) u beta) =ᵐ[
        signedTV mu] fun beta =>
          (u 1 - u 0) * (Ioi (finiteParam r)).indicator singularWeight beta := by
      filter_upwards [hAE] with beta hbeta
      rcases lt_or_gt_of_ne hbeta with hlt | hgt
      · have hkbeta : twoDominanceMap r beta = 0 := by
          simp [twoDominanceMap, hlt]
        have hnotIoi : ¬finiteParam r < beta := not_lt.mpr hlt.le
        rw [blockLimitFirst, hkbeta, hk1]
        simp [hnotIoi]
      · have hnlt : ¬beta < finiteParam r := not_lt.mpr hgt.le
        have hkbeta : twoDominanceMap r beta = 1 := by
          simp [twoDominanceMap, hnlt]
        rw [blockLimitFirst, hkbeta, hk1]
        simp [hgt]
        ring
    have hSecondAE : (fun beta => blockLimitSecond (twoDominanceMap r) u beta) =ᵐ[
        signedTV mu] fun beta =>
          ((u 0) ^ 2 - (u 1) ^ 2) *
            (Ioi (finiteParam r)).indicator singularWeight beta := by
      filter_upwards [hAE] with beta hbeta
      rcases lt_or_gt_of_ne hbeta with hlt | hgt
      · have hkbeta : twoDominanceMap r beta = 0 := by
          simp [twoDominanceMap, hlt]
        have hnotIoi : ¬finiteParam r < beta := not_lt.mpr hlt.le
        rw [blockLimitSecond, hkbeta, hk1]
        simp [hnotIoi]
      · have hnlt : ¬beta < finiteParam r := not_lt.mpr hgt.le
        have hkbeta : twoDominanceMap r beta = 1 := by
          simp [twoDominanceMap, hnlt]
        rw [blockLimitSecond, hkbeta, hk1]
        simp [hgt]
        ring
    constructor
    · rw [signedIntegral_congr_ae mu hFirstAE, signedIntegral_smul]
      simp only [twoUpperGFirst, upperMoment]
      ring
    · rw [signedIntegral_congr_ae mu hSecondAE, signedIntegral_smul]
      simp only [twoUpperGSecond, upperMoment]
      ring
  · intro hr1
    have hk1 := twoDominanceMap_one_of_gt hr1
    have hFirstAE : (fun beta => blockLimitFirst (twoDominanceMap r) u beta) =ᵐ[
        signedTV mu] fun beta =>
          (u 0 - u 1) * (Iio (finiteParam r)).indicator singularWeight beta := by
      filter_upwards [hAE] with beta hbeta
      rcases lt_or_gt_of_ne hbeta with hlt | hgt
      · have hkbeta : twoDominanceMap r beta = 0 := by
          simp [twoDominanceMap, hlt]
        rw [blockLimitFirst, hkbeta, hk1]
        simp [hlt]
        ring
      · have hnlt : ¬beta < finiteParam r := not_lt.mpr hgt.le
        have hkbeta : twoDominanceMap r beta = 1 := by
          simp [twoDominanceMap, hnlt]
        have hnotIio : ¬beta < finiteParam r := hnlt
        rw [blockLimitFirst, hkbeta, hk1]
        simp [hnotIio]
    have hSecondAE : (fun beta => blockLimitSecond (twoDominanceMap r) u beta) =ᵐ[
        signedTV mu] fun beta =>
          ((u 1) ^ 2 - (u 0) ^ 2) *
            (Iio (finiteParam r)).indicator singularWeight beta := by
      filter_upwards [hAE] with beta hbeta
      rcases lt_or_gt_of_ne hbeta with hlt | hgt
      · have hkbeta : twoDominanceMap r beta = 0 := by
          simp [twoDominanceMap, hlt]
        rw [blockLimitSecond, hkbeta, hk1]
        simp [hlt]
        ring
      · have hnlt : ¬beta < finiteParam r := not_lt.mpr hgt.le
        have hkbeta : twoDominanceMap r beta = 1 := by
          simp [twoDominanceMap, hnlt]
        have hnotIio : ¬beta < finiteParam r := hnlt
        rw [blockLimitSecond, hkbeta, hk1]
        simp [hnotIio]
    constructor
    · rw [signedIntegral_congr_ae mu hFirstAE, signedIntegral_smul]
      simp only [twoLowerGFirst, lowerMoment]
      ring
    · rw [signedIntegral_congr_ae mu hSecondAE, signedIntegral_smul]
      simp only [twoLowerGSecond, lowerMoment]
      ring

/-- Evaluation of the three-block pointwise limit kernels against the signed
parameter measure (`lem:three-block-limit-integral-eval`). -/
theorem threeBlockLimitIntegralEval
    (mu : SignedMeasure Param) (a b : ℝ)
    (ha : 0 < a) (hab : a < b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (u : Fin 3 → ℝ)
    (hmuA : signedTV mu ({finiteParam a} : Set Param) = 0)
    (hmuB : signedTV mu ({finiteParam b} : Set Param) = 0) :
    signedIntegral mu (fun beta =>
      blockLimitFirst (threeDominanceMap a b) u beta) =
        threeGFirst mu a b u ∧
    signedIntegral mu (fun beta =>
      blockLimitSecond (threeDominanceMap a b) u beta) =
        threeGSecond mu a b u := by
  have hAEA : ∀ᵐ beta ∂signedTV mu, beta ≠ finiteParam a := by
    simpa only [mem_singleton_iff, not_false_eq_true] using
      (measure_eq_zero_iff_ae_notMem.mp hmuA)
  have hAEB : ∀ᵐ beta ∂signedTV mu, beta ≠ finiteParam b := by
    simpa only [mem_singleton_iff, not_false_eq_true] using
      (measure_eq_zero_iff_ae_notMem.mp hmuB)
  have hFirstAE :
      (fun beta => blockLimitFirst (threeDominanceMap a b) u beta) =ᵐ[
        signedTV mu] fun beta =>
          ∑ j ∈ Finset.univ.erase (threeNormBlock a b),
            (u j - u (threeNormBlock a b)) * threeCellWeight a b j beta := by
    filter_upwards [hAEA, hAEB] with beta hbetaA hbetaB
    exact blockLimitFirst_three_eq_sum a b ha hab u beta hbetaA hbetaB
  have hSecondAE :
      (fun beta => blockLimitSecond (threeDominanceMap a b) u beta) =ᵐ[
        signedTV mu] fun beta =>
          ∑ j ∈ Finset.univ.erase (threeNormBlock a b),
            ((u (threeNormBlock a b)) ^ 2 - (u j) ^ 2) *
              threeCellWeight a b j beta := by
    filter_upwards [hAEA, hAEB] with beta hbetaA hbetaB
    exact blockLimitSecond_three_eq_sum a b ha hab u beta hbetaA hbetaB
  have hFirstPos : ∀ j ∈ Finset.univ.erase (threeNormBlock a b),
      Integrable
        (fun beta => (u j - u (threeNormBlock a b)) * threeCellWeight a b j beta)
        (signedPos mu) := by
    intro j hj
    exact (integrable_threeCellWeight_off_norm (signedPos mu) a b ha hab ha1 hb1 j
      (Finset.ne_of_mem_erase hj)).const_mul _
  have hFirstNeg : ∀ j ∈ Finset.univ.erase (threeNormBlock a b),
      Integrable
        (fun beta => (u j - u (threeNormBlock a b)) * threeCellWeight a b j beta)
        (signedNeg mu) := by
    intro j hj
    exact (integrable_threeCellWeight_off_norm (signedNeg mu) a b ha hab ha1 hb1 j
      (Finset.ne_of_mem_erase hj)).const_mul _
  have hSecondPos : ∀ j ∈ Finset.univ.erase (threeNormBlock a b),
      Integrable
        (fun beta => ((u (threeNormBlock a b)) ^ 2 - (u j) ^ 2) *
          threeCellWeight a b j beta) (signedPos mu) := by
    intro j hj
    exact (integrable_threeCellWeight_off_norm (signedPos mu) a b ha hab ha1 hb1 j
      (Finset.ne_of_mem_erase hj)).const_mul _
  have hSecondNeg : ∀ j ∈ Finset.univ.erase (threeNormBlock a b),
      Integrable
        (fun beta => ((u (threeNormBlock a b)) ^ 2 - (u j) ^ 2) *
          threeCellWeight a b j beta) (signedNeg mu) := by
    intro j hj
    exact (integrable_threeCellWeight_off_norm (signedNeg mu) a b ha hab ha1 hb1 j
      (Finset.ne_of_mem_erase hj)).const_mul _
  constructor
  · calc
      signedIntegral mu (fun beta =>
          blockLimitFirst (threeDominanceMap a b) u beta) =
          signedIntegral mu (fun beta =>
            ∑ j ∈ Finset.univ.erase (threeNormBlock a b),
              (u j - u (threeNormBlock a b)) * threeCellWeight a b j beta) :=
        signedIntegral_congr_ae mu hFirstAE
      _ = ∑ j ∈ Finset.univ.erase (threeNormBlock a b),
          signedIntegral mu (fun beta =>
            (u j - u (threeNormBlock a b)) * threeCellWeight a b j beta) :=
        signedIntegral_finset_sum mu _ _ hFirstPos hFirstNeg
      _ = threeGFirst mu a b u := by
        simp_rw [signedIntegral_smul, signedIntegral_threeCellWeight]
        simp only [threeGFirst]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  · calc
      signedIntegral mu (fun beta =>
          blockLimitSecond (threeDominanceMap a b) u beta) =
          signedIntegral mu (fun beta =>
            ∑ j ∈ Finset.univ.erase (threeNormBlock a b),
              ((u (threeNormBlock a b)) ^ 2 - (u j) ^ 2) *
                threeCellWeight a b j beta) :=
        signedIntegral_congr_ae mu hSecondAE
      _ = ∑ j ∈ Finset.univ.erase (threeNormBlock a b),
          signedIntegral mu (fun beta =>
            ((u (threeNormBlock a b)) ^ 2 - (u j) ^ 2) *
              threeCellWeight a b j beta) :=
        signedIntegral_finset_sum mu _ _ hSecondPos hSecondNeg
      _ = threeGSecond mu a b u := by
        simp_rw [signedIntegral_smul, signedIntegral_threeCellWeight]
        simp only [threeGSecond]
        apply Finset.sum_congr rfl
        intro j hj
        ring

end ConditionalEntropy
