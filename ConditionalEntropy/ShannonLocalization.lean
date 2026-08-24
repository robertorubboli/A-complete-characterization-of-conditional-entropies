import ConditionalEntropy.BlockLocalization
import ConditionalEntropy.ShannonDedicatedEscort
import ConditionalEntropy.ShannonExpansion
import ConditionalEntropy.ShannonKernelRegularityBridge
import ConditionalEntropy.ShannonLogMass
import ConditionalEntropy.UniformSignedDCT

/-!
# Shannon-point localization

This module passes the two dedicated Shannon derivative kernels through a
finite signed parameter measure and then transfers the resulting limits from
the norm-free column to the logarithmic column.  The atom at order one is kept
explicit; the crossing at `theta.c` is discarded only through the stated
total-variation null hypothesis.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

private def shannonLimitVelocity (z : ℝ × ℝ) : Fin 2 → ℝ := ![0, z.2]

private def shannonAtomTerm (z : ℝ × ℝ) (beta : Param) : ℝ :=
  ({(1 : Param)} : Set Param).indicator (fun _ ↦ z.1) beta

/-- Pointwise first-kernel limit, totalized to zero at the null crossing. -/
private def shannonPointFirst (theta : ShannonData) (z : ℝ × ℝ)
    (beta : Param) : ℝ :=
  if beta = finiteParam theta.c then 0
  else shannonAtomTerm z beta +
    blockLimitFirst (twoDominanceMap theta.c) (shannonLimitVelocity z) beta

/-- Pointwise second-kernel limit, totalized to zero at the null crossing. -/
private def shannonPointSecond (theta : ShannonData) (z : ℝ × ℝ)
    (beta : Param) : ℝ :=
  if beta = finiteParam theta.c then 0
  else blockLimitSecond (twoDominanceMap theta.c) (shannonLimitVelocity z) beta

private theorem continuous_shannonKernels_param_local
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) :
    Continuous (fun beta : Param ↦ shannonKOne theta n z beta) ∧
      Continuous (fun beta : Param ↦ shannonKTwo theta n z beta) := by
  letI := shannonIndexNonempty theta n
  let L := shannonLineData theta n z
  obtain ⟨epsilon0, hepsilon0, hfixed0⟩ :=
    exists_fixedMaxCoordinate_shannonLine theta n z
  let epsilon := epsilon0 / 2
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  have hsubset : Icc (-epsilon) epsilon ⊆ Ioo (-epsilon0) epsilon0 := by
    intro lambda hlambda
    constructor
    · calc
        -epsilon0 < -(epsilon0 / 2) := by linarith
        _ ≤ lambda := by simpa only [epsilon] using hlambda.1
    · calc
        lambda ≤ epsilon0 / 2 := by simpa only [epsilon] using hlambda.2
        _ < epsilon0 := by linarith
  have hfixed : FixedMaxCoordinate L (Icc (-epsilon) epsilon)
      (shannonRepresentative theta n 2) := by
    intro lambda hlambda
    exact hfixed0 lambda (hsubset hlambda)
  have hpos : ∀ lambda ∈ Icc (-epsilon) epsilon, LinePositive L lambda := by
    intro lambda hlambda
    exact (hfixed lambda hlambda).1
  have hbundle := continuousOn_entropyLine_full_bundle L hepsilon hpos hfixed
  have hzero : (0 : ℝ) ∈ Icc (-epsilon) epsilon := by
    constructor <;> linarith
  have hsectionOne : Continuous
      (fun beta : Param ↦ entropyLineFirst L beta 0) := by
    rw [← continuousOn_univ]
    apply hbundle.2.1.comp
      (continuous_id.prodMk continuous_const).continuousOn
    intro beta _hbeta
    exact ⟨mem_univ beta, hzero⟩
  have hsectionTwo : Continuous
      (fun beta : Param ↦ entropyLineSecond L beta 0) := by
    rw [← continuousOn_univ]
    apply hbundle.2.2.comp
      (continuous_id.prodMk continuous_const).continuousOn
    intro beta _hbeta
    exact ⟨mem_univ beta, hzero⟩
  simpa only [shannonKOne, shannonKTwo, L] using
    And.intro hsectionOne hsectionTwo

private theorem measurable_shannonPointFirst (theta : ShannonData)
    (z : ℝ × ℝ) : Measurable (shannonPointFirst theta z) := by
  unfold shannonPointFirst
  apply Measurable.ite (measurableSet_singleton (finiteParam theta.c))
  · exact measurable_const
  · exact (measurable_const.indicator (measurableSet_singleton (1 : Param))).add
      (measurable_blockLimitFirst (measurable_twoDominanceMap theta.c)
        (shannonLimitVelocity z))

private theorem measurable_shannonPointSecond (theta : ShannonData)
    (z : ℝ × ℝ) : Measurable (shannonPointSecond theta z) := by
  unfold shannonPointSecond
  apply Measurable.ite (measurableSet_singleton (finiteParam theta.c))
  · exact measurable_const
  · exact measurable_blockLimitSecond (measurable_twoDominanceMap theta.c)
      (shannonLimitVelocity z)

private def shannonLocalDelta (theta : ShannonData) : ℝ :=
  min (1 / 4 : ℝ) ((theta.c - 1) / 8)

private theorem shannonLocalDelta_pos (theta : ShannonData) :
    0 < shannonLocalDelta theta := by
  unfold shannonLocalDelta
  exact lt_min (by norm_num) (div_pos (sub_pos.mpr theta.c_gt_one) (by norm_num))

private theorem shannonLocalDelta_lt (theta : ShannonData) :
    shannonLocalDelta theta < min (1 / 2 : ℝ) ((theta.c - 1) / 4) := by
  rw [lt_min_iff]
  constructor
  · exact (min_le_left _ _).trans_lt (by norm_num)
  · exact (min_le_right _ _).trans_lt (by
      have hc : 0 < theta.c - 1 := sub_pos.mpr theta.c_gt_one
      linarith)

private theorem compactUniformError_bounds_of_point_bound
    {U : Type*} (K : Set U) (hK0 : K.Nonempty)
    (fN : ℕ → U → ℝ) (f : U → ℝ) (n : ℕ) (B : ℝ)
    (hB : ∀ x ∈ K, |fN n x - f x| ≤ B) :
    0 ≤ compactUniformError K fN f n ∧
      compactUniformError K fN f n ≤ B := by
  unfold compactUniformError
  obtain ⟨x, hx⟩ := hK0
  have hmem : |fN n x - f x| ∈
      {r : ℝ | ∃ y ∈ K, r = |fN n y - f y|} := ⟨x, hx, rfl⟩
  have hbdd : BddAbove {r : ℝ | ∃ y ∈ K, r = |fN n y - f y|} := by
    refine ⟨B, ?_⟩
    rintro r ⟨y, hy, rfl⟩
    exact hB y hy
  constructor
  · exact (abs_nonneg _).trans (le_csSup hbdd hmem)
  · exact csSup_le ⟨_, hmem⟩ fun _ hr ↦ by
      rcases hr with ⟨y, hy, rfl⟩
      exact hB y hy

private theorem exists_compact_pair_abs_bound_local (K : Set (ℝ × ℝ))
    (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, |z.1| ≤ B ∧ |z.2| ≤ B := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ × ℝ)
  let B := max R 0
  have hB : 0 ≤ B := le_max_right R 0
  refine ⟨B, hB, ?_⟩
  intro z hz
  have hznorm : ‖z‖ ≤ R := by
    simpa [dist_zero_right] using hR hz
  exact ⟨(by
      calc
        |z.1| = ‖z.1‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖z‖ := norm_fst_le z
        _ ≤ R := hznorm
        _ ≤ B := le_max_left R 0),
    (by
      calc
        |z.2| = ‖z.2‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖z‖ := norm_snd_le z
        _ ≤ R := hznorm
        _ ≤ B := le_max_left R 0)⟩

@[simp] private theorem shannonKOne_zero_local (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) : shannonKOne theta n z 0 = 0 := by
  letI := shannonIndexNonempty theta n
  unfold shannonKOne
  exact entropyLineFirst_zero _ (linePositiveZero _)

private theorem shannonVar_le_four_sq (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha U : ℝ) (hU : 0 ≤ U)
    (hu : ∀ j : Fin 3, |shannonBlockVelocity theta n z j| ≤ U) :
    shannonVar theta n z alpha ≤ 4 * U ^ 2 := by
  have h := shannonVar_le_outside theta n z alpha 0 U hU hu
  calc
    shannonVar theta n z alpha ≤
        (4 * U ^ 2) *
          (∑ j ∈ Finset.univ.erase 0, shannonEscort theta n z j alpha) := h
    _ ≤ (4 * U ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left
        (shannonOutsideMass_le_one theta n z 0 alpha) (by positivity)
    _ = 4 * U ^ 2 := mul_one _

private theorem finiteShannonKernelCrudeBounds (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (U A delta alpha : ℝ)
    (hU : 0 ≤ U)
    (hu : ∀ j : Fin 3, |shannonBlockVelocity theta n z j| ≤ U)
    (hAlpha : 0 < alpha) (hAlphaA : alpha ≤ A)
    (hDelta : 0 < delta) (hAway : delta ≤ |alpha - 1|) :
    |shannonKOne theta n z (finiteParam alpha)| ≤
        2 * U * (A / delta) ∧
      |shannonKTwo theta n z (finiteParam alpha)| ≤
        4 * A * U ^ 2 + 2 * U ^ 2 * (A / delta) := by
  have hOne : alpha ≠ 1 := by
    intro h
    subst alpha
    have hzero : delta ≤ 0 := by simpa using hAway
    exact (not_le_of_gt hDelta hzero).elim
  have hA : 0 ≤ A := hAlpha.le.trans hAlphaA
  have hW : 0 ≤ A / delta := div_nonneg hA hDelta.le
  have hWeight : |singularWeight (finiteParam alpha)| ≤ A / delta := by
    rw [singularWeight_finite hAlpha.le hOne, abs_div, abs_of_pos hAlpha,
      abs_sub_comm]
    exact (div_le_div_iff₀ (lt_of_lt_of_le hDelta hAway) hDelta).2
      (mul_le_mul hAlphaA hAway hDelta.le hA)
  have hMeanAlpha := abs_shannonMean_le theta n z alpha U hu
  have hMeanOne := abs_shannonMean_le theta n z 1 U hu
  have hMeanDiff :
      |shannonMean theta n z alpha - shannonMean theta n z 1| ≤ 2 * U := by
    calc
      _ ≤ |shannonMean theta n z alpha| + |shannonMean theta n z 1| :=
        abs_sub _ _
      _ ≤ U + U := add_le_add hMeanAlpha hMeanOne
      _ = 2 * U := by ring
  have hSqDiff :
      |shannonMean theta n z 1 ^ 2 - shannonMean theta n z alpha ^ 2| ≤
        2 * U ^ 2 := by
    calc
      _ ≤ |shannonMean theta n z 1 ^ 2| +
          |shannonMean theta n z alpha ^ 2| := abs_sub _ _
      _ = shannonMean theta n z 1 ^ 2 +
          shannonMean theta n z alpha ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
      _ ≤ U ^ 2 + U ^ 2 := by
        exact add_le_add
          (sq_le_sq.mpr (by simpa only [abs_of_nonneg hU] using hMeanOne))
          (sq_le_sq.mpr (by simpa only [abs_of_nonneg hU] using hMeanAlpha))
      _ = 2 * U ^ 2 := by ring
  have hVar := shannonVar_le_four_sq theta n z alpha U hU hu
  constructor
  · rw [shannonKOne_finite theta n z hAlpha hOne, abs_mul]
    calc
      |singularWeight (finiteParam alpha)| *
          |shannonMean theta n z alpha - shannonMean theta n z 1| ≤
        (A / delta) * (2 * U) :=
          mul_le_mul hWeight hMeanDiff (abs_nonneg _) hW
      _ = 2 * U * (A / delta) := by ring
  · rw [shannonKTwo_finite theta n z hAlpha hOne]
    calc
      |-alpha * shannonVar theta n z alpha +
          singularWeight (finiteParam alpha) *
            (shannonMean theta n z 1 ^ 2 -
              shannonMean theta n z alpha ^ 2)| ≤
        |-alpha * shannonVar theta n z alpha| +
          |singularWeight (finiteParam alpha) *
            (shannonMean theta n z 1 ^ 2 -
              shannonMean theta n z alpha ^ 2)| := abs_add_le _ _
      _ ≤ alpha * (4 * U ^ 2) + (A / delta) * (2 * U ^ 2) := by
        rw [abs_mul, abs_neg, abs_of_pos hAlpha,
          abs_of_nonneg (shannonVar_nonneg theta n z alpha), abs_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hVar hAlpha.le)
          (mul_le_mul hWeight hSqDiff (abs_nonneg _) hW)
      _ ≤ A * (4 * U ^ 2) + (A / delta) * (2 * U ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_right hAlphaA (by positivity)) le_rfl
      _ = 4 * A * U ^ 2 + 2 * U ^ 2 * (A / delta) := by ring

private theorem exists_uniform_shannonKernel_bound_at (theta : ShannonData)
    (z : ℝ × ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ beta : Param,
      |shannonKOne theta n z beta| ≤ C ∧
        |shannonKTwo theta n z beta| ≤ C := by
  let K : Set (ℝ × ℝ) := {z}
  let delta := shannonLocalDelta theta
  have hK : IsCompact K := isCompact_singleton
  have hK0 : K.Nonempty := singleton_nonempty z
  have hdelta0 : 0 < delta := shannonLocalDelta_pos theta
  have hdelta : delta < min (1 / 2 : ℝ) ((theta.c - 1) / 4) :=
    shannonLocalDelta_lt theta
  obtain ⟨Cnear, hCnear, hnear, _hnearConv, _honeFirst, _honeSecond⟩ :=
    shannonNeighbourhood theta K delta hK hK0 hdelta0 hdelta
  obtain ⟨A, gamma, Ctail, hAc, _hgamma, hCtail, htail⟩ :=
    shannonDedicatedEscortTail theta K hK hK0
  obtain ⟨U, hU, hu⟩ := exists_uniform_shannonVelocity_bound theta K hK
  have hA : 0 ≤ A := by linarith [theta.c_gt_one]
  let Cfirst : ℝ := 2 * U * (A / delta)
  let Csecond : ℝ := 4 * A * U ^ 2 + 2 * U ^ 2 * (A / delta)
  let C : ℝ := Cnear + Ctail + Cfirst + Csecond
  have hCfirst : 0 ≤ Cfirst := by
    dsimp only [Cfirst]
    positivity
  have hCsecond : 0 ≤ Csecond := by
    dsimp only [Csecond]
    exact add_nonneg (by positivity)
      (mul_nonneg (by positivity) (div_nonneg hA hdelta0.le))
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hNearC : Cnear ≤ C := by
    dsimp only [C]
    linarith
  have hTailC : Ctail ≤ C := by
    dsimp only [C]
    linarith
  have hFirstC : Cfirst ≤ C := by
    dsimp only [C]
    linarith
  have hSecondC : Csecond ≤ C := by
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro n beta
  by_cases hbetaTop : beta = (⊤ : Param)
  · subst beta
    have ht := htail n z (by rfl) A le_rfl
    exact ⟨ht.2.2.2.2.1.trans hTailC, ht.2.2.2.2.2.trans hTailC⟩
  let alpha := ENNReal.toReal beta
  have hAlpha0 : 0 ≤ alpha := ENNReal.toReal_nonneg
  have hback : finiteParam alpha = beta := by
    simpa only [alpha, paramToReal] using finiteParam_paramToReal beta hbetaTop
  by_cases hAlphaZero : alpha = 0
  · have hbetaZero : beta = 0 := by
      rw [← hback, hAlphaZero, finiteParam_zero]
    rw [hbetaZero, shannonKOne_zero_local, shannonKTwo_zero, abs_zero]
    exact ⟨hC, hC⟩
  have hAlphaPos : 0 < alpha := lt_of_le_of_ne hAlpha0 (Ne.symm hAlphaZero)
  by_cases hAlphaNear : alpha ∈ Icc (1 - delta) (1 + delta)
  · have hn := hnear n z (by rfl) alpha hAlphaNear
    rw [← hback]
    exact ⟨hn.1.trans hNearC, hn.2.trans hNearC⟩
  by_cases hAlphaLarge : A ≤ alpha
  · have ht := htail n z (by rfl) alpha hAlphaLarge
    rw [← hback]
    exact ⟨ht.2.2.1.trans hTailC, ht.2.2.2.1.trans hTailC⟩
  have hAlphaA : alpha ≤ A := le_of_not_ge hAlphaLarge
  have hAway : delta ≤ |alpha - 1| := by
    simp only [mem_Icc, not_and_or, not_le] at hAlphaNear
    rcases hAlphaNear with hleft | hright
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  have hm := finiteShannonKernelCrudeBounds theta n z U A delta alpha hU
    (hu n z (by rfl)) hAlphaPos hAlphaA hdelta0 hAway
  rw [← hback]
  exact ⟨hm.1.trans hFirstC, hm.2.trans hSecondC⟩

private theorem shannonPointFirst_one (theta : ShannonData) (z : ℝ × ℝ) :
    shannonPointFirst theta z 1 = z.1 := by
  have hne : (1 : Param) ≠ finiteParam theta.c := by
    intro h
    have hfinite : finiteParam 1 = finiteParam theta.c := by
      simpa only [finiteParam_one] using h
    have hc := finiteParam_injectiveOn_nonneg
      (show (1 : ℝ) ∈ Ici 0 from by
        simpa only [mem_Ici] using zero_le_one)
      (show theta.c ∈ Ici (0 : ℝ) from
        (zero_lt_one.trans theta.c_gt_one).le) hfinite
    linarith [theta.c_gt_one]
  simp [shannonPointFirst, hne, shannonAtomTerm, blockLimitFirst]

private theorem shannonPointSecond_one (theta : ShannonData) (z : ℝ × ℝ) :
    shannonPointSecond theta z 1 = 0 := by
  have hne : (1 : Param) ≠ finiteParam theta.c := by
    intro h
    have hfinite : finiteParam 1 = finiteParam theta.c := by
      simpa only [finiteParam_one] using h
    have hc := finiteParam_injectiveOn_nonneg
      (show (1 : ℝ) ∈ Ici 0 from by
        simpa only [mem_Ici] using zero_le_one)
      (show theta.c ∈ Ici (0 : ℝ) from
        (zero_lt_one.trans theta.c_gt_one).le) hfinite
    linarith [theta.c_gt_one]
  simp [shannonPointSecond, hne, blockLimitSecond]

private theorem shannonPointFirst_zero (theta : ShannonData) (z : ℝ × ℝ) :
    shannonPointFirst theta z 0 = 0 := by
  have hc0 : finiteParam theta.c ≠ 0 :=
    (finiteParam_eq_zero_iff.not.mpr (not_le_of_gt (zero_lt_one.trans theta.c_gt_one)))
  simp [shannonPointFirst, hc0.symm, shannonAtomTerm, blockLimitFirst,
    twoDominanceMap]

private theorem shannonPointSecond_zero (theta : ShannonData) (z : ℝ × ℝ) :
    shannonPointSecond theta z 0 = 0 := by
  have hc0 : finiteParam theta.c ≠ 0 :=
    (finiteParam_eq_zero_iff.not.mpr (not_le_of_gt (zero_lt_one.trans theta.c_gt_one)))
  simp [shannonPointSecond, hc0.symm, blockLimitSecond, twoDominanceMap]

private theorem shannonPointFirst_top (theta : ShannonData) (z : ℝ × ℝ) :
    shannonPointFirst theta z ⊤ = -z.2 := by
  have h1c : (1 : Param) < finiteParam theta.c := by
    rw [← finiteParam_one]
    exact (ENNReal.ofReal_lt_ofReal_iff
      (zero_lt_one.trans theta.c_gt_one)).2 theta.c_gt_one
  have htopc : (⊤ : Param) ≠ finiteParam theta.c :=
    (finiteParam_ne_top theta.c).symm
  simp [shannonPointFirst, shannonAtomTerm, blockLimitFirst,
    shannonLimitVelocity, twoDominanceMap, h1c, htopc]

private theorem shannonPointSecond_top (theta : ShannonData) (z : ℝ × ℝ) :
    shannonPointSecond theta z ⊤ = z.2 ^ 2 := by
  have h1c : (1 : Param) < finiteParam theta.c := by
    rw [← finiteParam_one]
    exact (ENNReal.ofReal_lt_ofReal_iff
      (zero_lt_one.trans theta.c_gt_one)).2 theta.c_gt_one
  have htopc : (⊤ : Param) ≠ finiteParam theta.c :=
    (finiteParam_ne_top theta.c).symm
  simp [shannonPointSecond, blockLimitSecond, shannonLimitVelocity,
    twoDominanceMap, h1c, htopc]

private theorem shannonPointFirst_formula (theta : ShannonData)
    (z : ℝ × ℝ) :
    shannonPointFirst theta z = fun beta ↦
      shannonAtomTerm z beta +
        z.2 * (Ioi (finiteParam theta.c)).indicator singularWeight beta := by
  funext beta
  have h1c : (1 : Param) < finiteParam theta.c := by
    rw [← finiteParam_one]
    exact (ENNReal.ofReal_lt_ofReal_iff
      (zero_lt_one.trans theta.c_gt_one)).2 theta.c_gt_one
  have hkOne : twoDominanceMap theta.c 1 = 0 := by
    simp only [twoDominanceMap, if_pos h1c]
  by_cases hbetaC : beta = finiteParam theta.c
  · subst beta
    simp [shannonPointFirst, shannonAtomTerm, h1c.ne']
  · rcases lt_or_gt_of_ne hbetaC with hbelow | habove
    · have hkBeta : twoDominanceMap theta.c beta = 0 := by
        simp only [twoDominanceMap, if_pos hbelow]
      have hnotTail : beta ∉ Ioi (finiteParam theta.c) :=
        not_lt.mpr hbelow.le
      rw [shannonPointFirst, if_neg hbetaC, blockLimitFirst, hkBeta, hkOne,
        Set.indicator_of_notMem hnotTail]
      simp [shannonLimitVelocity]
    · have hkBeta : twoDominanceMap theta.c beta = 1 := by
        simp only [twoDominanceMap, if_neg (not_lt.mpr habove.le)]
      have hind : (Ioi (finiteParam theta.c)).indicator singularWeight beta =
          singularWeight beta := Set.indicator_of_mem
            (show beta ∈ Ioi (finiteParam theta.c) from habove) singularWeight
      rw [shannonPointFirst, if_neg hbetaC, blockLimitFirst, hkBeta, hkOne,
        hind]
      simp [shannonLimitVelocity]
      ring

private theorem shannonPointSecond_formula (theta : ShannonData)
    (z : ℝ × ℝ) :
    shannonPointSecond theta z = fun beta ↦
      -(z.2 ^ 2) *
        (Ioi (finiteParam theta.c)).indicator singularWeight beta := by
  funext beta
  have h1c : (1 : Param) < finiteParam theta.c := by
    rw [← finiteParam_one]
    exact (ENNReal.ofReal_lt_ofReal_iff
      (zero_lt_one.trans theta.c_gt_one)).2 theta.c_gt_one
  have hkOne : twoDominanceMap theta.c 1 = 0 := by
    simp only [twoDominanceMap, if_pos h1c]
  by_cases hbetaC : beta = finiteParam theta.c
  · subst beta
    simp [shannonPointSecond]
  · rcases lt_or_gt_of_ne hbetaC with hbelow | habove
    · have hkBeta : twoDominanceMap theta.c beta = 0 := by
        simp only [twoDominanceMap, if_pos hbelow]
      have hnotTail : beta ∉ Ioi (finiteParam theta.c) :=
        not_lt.mpr hbelow.le
      rw [shannonPointSecond, if_neg hbetaC, blockLimitSecond, hkBeta, hkOne,
        Set.indicator_of_notMem hnotTail]
      simp [shannonLimitVelocity]
    · have hkBeta : twoDominanceMap theta.c beta = 1 := by
        simp only [twoDominanceMap, if_neg (not_lt.mpr habove.le)]
      have hind : (Ioi (finiteParam theta.c)).indicator singularWeight beta =
          singularWeight beta := Set.indicator_of_mem
            (show beta ∈ Ioi (finiteParam theta.c) from habove) singularWeight
      rw [shannonPointSecond, if_neg hbetaC, blockLimitSecond, hkBeta, hkOne,
        hind]
      simp [shannonLimitVelocity]
      ring

private theorem integrable_shannonAtomTerm
    (nu : Measure Param) [IsFiniteMeasure nu] (z : ℝ × ℝ) :
    Integrable (shannonAtomTerm z) nu := by
  unfold shannonAtomTerm
  exact (integrable_const z.1).indicator
    (measurableSet_singleton (1 : Param))

private theorem signedIntegral_shannonAtomTerm
    (mu : SignedMeasure Param) (z : ℝ × ℝ) :
    signedIntegral mu (shannonAtomTerm z) = signedAtom mu 1 * z.1 := by
  have heq : shannonAtomTerm z = fun beta ↦
      z.1 * (({(1 : Param)} : Set Param).indicator (fun _ ↦ 1) beta) := by
    funext beta
    by_cases hbeta : beta ∈ ({(1 : Param)} : Set Param)
    · simp [shannonAtomTerm, hbeta]
    · simp [shannonAtomTerm, hbeta]
  rw [heq, signedIntegral_smul]
  unfold signedAtom
  ring

private theorem signedIntegral_shannonPointFirst
    (mu : SignedMeasure Param) (theta : ShannonData) (z : ℝ × ℝ) :
    signedIntegral mu (shannonPointFirst theta z) =
      shannonLimitFirst mu theta z := by
  rw [shannonPointFirst_formula]
  have hAtomPos := integrable_shannonAtomTerm (signedPos mu) z
  have hAtomNeg := integrable_shannonAtomTerm (signedNeg mu) z
  have hTailPos :=
    (integrable_singularWeight_Ioi (signedPos mu) theta.c_gt_one).const_mul z.2
  have hTailNeg :=
    (integrable_singularWeight_Ioi (signedNeg mu) theta.c_gt_one).const_mul z.2
  rw [signedIntegral_add mu hAtomPos hAtomNeg hTailPos hTailNeg,
    signedIntegral_shannonAtomTerm, signedIntegral_smul]
  unfold shannonLimitFirst shannonTailMoment upperMoment
  ring

private theorem signedIntegral_shannonPointSecond
    (mu : SignedMeasure Param) (theta : ShannonData) (z : ℝ × ℝ) :
    signedIntegral mu (shannonPointSecond theta z) =
      shannonLimitSecond mu theta z := by
  rw [shannonPointSecond_formula, signedIntegral_smul]
  unfold shannonLimitSecond shannonTailMoment upperMoment
  ring

private theorem shannonPoint_finite_of_lt (theta : ShannonData)
    (z : ℝ × ℝ) {alpha : ℝ} (hAlpha : 0 < alpha)
    (hOne : alpha ≠ 1) (hC : alpha < theta.c) :
    shannonPointFirst theta z (finiteParam alpha) = 0 ∧
      shannonPointSecond theta z (finiteParam alpha) = 0 := by
  have hAlphaC : finiteParam alpha < finiteParam theta.c :=
    (ENNReal.ofReal_lt_ofReal_iff
      (zero_lt_one.trans theta.c_gt_one)).2 hC
  have hAlphaOne : finiteParam alpha ≠ (1 : Param) := by
    intro h
    have heq : finiteParam alpha = finiteParam 1 := by
      simpa only [finiteParam_one] using h
    exact hOne (finiteParam_injectiveOn_nonneg
      (show alpha ∈ Ici (0 : ℝ) from hAlpha.le)
      (show (1 : ℝ) ∈ Ici 0 from by
        simpa only [mem_Ici] using zero_le_one) heq)
  constructor
  · rw [shannonPointFirst_formula]
    simp [shannonAtomTerm, hAlphaOne, not_lt.mpr hAlphaC.le]
  · rw [shannonPointSecond_formula]
    simp [not_lt.mpr hAlphaC.le]

private theorem shannonPoint_finite_of_gt (theta : ShannonData)
    (z : ℝ × ℝ) {alpha : ℝ} (hC : theta.c < alpha) :
    shannonPointFirst theta z (finiteParam alpha) =
        singularWeight (finiteParam alpha) * z.2 ∧
      shannonPointSecond theta z (finiteParam alpha) =
        -singularWeight (finiteParam alpha) * z.2 ^ 2 := by
  have hAlpha : 0 < alpha := (zero_lt_one.trans theta.c_gt_one).trans hC
  have hOne : alpha ≠ 1 := by linarith [theta.c_gt_one]
  have hAlphaC : finiteParam theta.c < finiteParam alpha :=
    (ENNReal.ofReal_lt_ofReal_iff
      ((zero_lt_one.trans theta.c_gt_one).trans hC)).2 hC
  have hAlphaOne : finiteParam alpha ≠ (1 : Param) := by
    intro h
    have heq : finiteParam alpha = finiteParam 1 := by
      simpa only [finiteParam_one] using h
    exact hOne (finiteParam_injectiveOn_nonneg
      (show alpha ∈ Ici (0 : ℝ) from hAlpha.le)
      (show (1 : ℝ) ∈ Ici 0 from by
        simpa only [mem_Ici] using zero_le_one) heq)
  have hmem : finiteParam alpha ∈ Ioi (finiteParam theta.c) := hAlphaC
  constructor
  · rw [shannonPointFirst_formula]
    change shannonAtomTerm z (finiteParam alpha) +
        z.2 * (Ioi (finiteParam theta.c)).indicator singularWeight
          (finiteParam alpha) = singularWeight (finiteParam alpha) * z.2
    rw [Set.indicator_of_mem hmem]
    simp [shannonAtomTerm, hAlphaOne]
    ring
  · rw [shannonPointSecond_formula]
    change -z.2 ^ 2 * (Ioi (finiteParam theta.c)).indicator singularWeight
        (finiteParam alpha) = -singularWeight (finiteParam alpha) * z.2 ^ 2
    rw [Set.indicator_of_mem hmem]
    ring

private theorem tendsto_of_abs_sub_le_bound
    {f b : ℕ → ℝ} {a : ℝ}
    (hfb : ∀ n, |f n - a| ≤ b n)
    (hb : Tendsto b atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 a) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hdist : (fun n ↦ dist (f n) a) = fun n ↦ |f n - a| := by
    funext n
    exact Real.dist_eq (f n) a
  rw [hdist]
  apply squeeze_zero
  · exact fun n ↦ abs_nonneg _
  · exact hfb
  · exact hb

private theorem tendsto_shannonBlockVelocity_zero (theta : ShannonData)
    (z : ℝ × ℝ) :
    Tendsto (fun n ↦ shannonBlockVelocity theta n z 0) atTop (𝓝 0) := by
  have hscale : Tendsto (fun n : ℕ ↦ shannonScale n) atTop atTop := by
    have hbase : Tendsto (fun n : ℕ ↦ blockScale n) atTop atTop :=
      tendsto_blockScale_atTop
    simpa only [shannonScale] using hbase
  have hlog : Tendsto (fun n : ℕ ↦ shannonLogScale n) atTop atTop := by
    exact Real.tendsto_log_atTop.comp hscale
  have hinv : Tendsto (fun n : ℕ ↦ (shannonLogScale n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hconst : Tendsto (fun _ : ℕ ↦ z.1 / theta.q) atTop
      (𝓝 (z.1 / theta.q)) := tendsto_const_nhds
  convert hconst.mul hinv using 1
  · funext n
    rw [shannonBlockVelocity_zero]
    field_simp [theta.q_pos.ne', (shannonLogScale_pos n).ne']
  · simp

private theorem tendsto_shannonBlockVelocity_one (theta : ShannonData)
    (z : ℝ × ℝ) :
    Tendsto (fun n ↦ shannonBlockVelocity theta n z 1) atTop (𝓝 0) := by
  have hscale : Tendsto (fun n : ℕ ↦ shannonScale n) atTop atTop := by
    have hbase : Tendsto (fun n : ℕ ↦ blockScale n) atTop atTop :=
      tendsto_blockScale_atTop
    simpa only [shannonScale] using hbase
  have hlog : Tendsto (fun n : ℕ ↦ shannonLogScale n) atTop atTop := by
    exact Real.tendsto_log_atTop.comp hscale
  have hinv : Tendsto (fun n : ℕ ↦ (shannonLogScale n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hconst : Tendsto (fun _ : ℕ ↦ -z.1 / theta.p) atTop
      (𝓝 (-z.1 / theta.p)) := tendsto_const_nhds
  convert hconst.mul hinv using 1
  · funext n
    rw [shannonBlockVelocity_one]
    field_simp [theta.p_pos.ne', (shannonLogScale_pos n).ne']
  · simp

private theorem shannonDominantMomentTendsto (theta : ShannonData)
    (z : ℝ × ℝ) (alpha : ℝ) (k : Fin 3) (eta : ℝ)
    (heta : 0 < eta)
    (hgap : ∀ a ∈ ({alpha} : Set ℝ), ∀ j : Fin 3, j ≠ k →
      eta ≤ shannonExponent theta k a - shannonExponent theta j a) :
    Tendsto (fun n ↦ shannonMean theta n z alpha -
        shannonBlockVelocity theta n z k) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ shannonVar theta n z alpha) atTop (𝓝 0) := by
  obtain ⟨M, hM, hpref⟩ := exists_shannonPrefactor_ratio_bound theta
    ({alpha} : Set ℝ) isCompact_singleton (singleton_nonempty alpha) k
  obtain ⟨U, hU, hu⟩ := exists_uniform_shannonVelocity_bound theta
    ({z} : Set (ℝ × ℝ)) isCompact_singleton
  obtain ⟨_C_I, C_K, _hCI, hCK, hest⟩ :=
    shannonDominantEstimates theta ({alpha} : Set ℝ) k eta M U hM hU
      hpref hgap
  let b : ℕ → ℝ := fun n ↦
    C_K * Real.rpow (shannonScale n) (-eta)
  have hb0 : ∀ n, 0 ≤ b n := by
    intro n
    exact mul_nonneg hCK (Real.rpow_nonneg (shannonScale_pos n).le _)
  have hb : Tendsto b atTop (𝓝 0) := by
    have hscale : Tendsto (fun n : ℕ ↦ shannonScale n) atTop atTop := by
      have hbase : Tendsto (fun n : ℕ ↦ blockScale n) atTop atTop :=
        tendsto_blockScale_atTop
      simpa only [shannonScale] using hbase
    have hr : Tendsto (fun n : ℕ ↦ Real.rpow (shannonScale n) (-eta))
        atTop (𝓝 0) := by
      exact (tendsto_rpow_neg_atTop heta).comp hscale
    simpa only [b, mul_zero] using tendsto_const_nhds.mul hr
  have hpoint (n : ℕ) := hest n z (hu n z (by rfl)) alpha (by rfl)
  have hmean : ∀ n, |shannonMean theta n z alpha -
      shannonBlockVelocity theta n z k| ≤ b n := by
    intro n
    have hm := (hpoint n).2.1
    dsimp only [b]
    linarith [abs_nonneg (shannonSecond theta n z alpha -
      shannonBlockVelocity theta n z k ^ 2),
      shannonVar_nonneg theta n z alpha]
  have hvar : ∀ n, shannonVar theta n z alpha ≤ b n := by
    intro n
    have hm := (hpoint n).2.1
    dsimp only [b]
    linarith [abs_nonneg (shannonMean theta n z alpha -
      shannonBlockVelocity theta n z k),
      abs_nonneg (shannonSecond theta n z alpha -
        shannonBlockVelocity theta n z k ^ 2)]
  constructor
  · apply tendsto_of_abs_sub_le_bound
      (fun n ↦ by simpa only [sub_zero] using hmean n) hb
  · apply squeeze_zero
    · exact fun n ↦ shannonVar_nonneg theta n z alpha
    · exact hvar
    · exact hb

private theorem shannonMoments_tendsto_finite (theta : ShannonData)
    (z : ℝ × ℝ) {alpha : ℝ} (_hAlpha : 0 < alpha)
    (hOne : alpha ≠ 1) (hC : alpha ≠ theta.c) :
    (alpha < theta.c →
      Tendsto (fun n ↦ shannonMean theta n z alpha) atTop (𝓝 0)) ∧
    (theta.c < alpha →
      Tendsto (fun n ↦ shannonMean theta n z alpha) atTop (𝓝 z.2)) ∧
    Tendsto (fun n ↦ shannonVar theta n z alpha) atTop (𝓝 0) := by
  rcases lt_or_gt_of_ne hOne with hbelow | haboveOne
  · let eta : ℝ := 1 - alpha
    have heta : 0 < eta := sub_pos.mpr hbelow
    have hgap : ∀ a ∈ ({alpha} : Set ℝ), ∀ j : Fin 3, j ≠ 0 →
        eta ≤ shannonExponent theta 0 a - shannonExponent theta j a := by
      intro a ha j hj
      simp only [mem_singleton_iff] at ha
      subst a
      rcases j with ⟨j, hjlt⟩
      interval_cases j
      · exact (hj rfl).elim
      · simp [shannonExponent, shannonCountExponent, shannonAmplitude]
        dsimp only [eta]
        linarith
      · simp [shannonExponent, shannonCountExponent, shannonAmplitude]
        dsimp only [eta]
        linarith [theta.c_gt_one]
    have hm := shannonDominantMomentTendsto theta z alpha 0 eta heta hgap
    have hmean := hm.1.add (tendsto_shannonBlockVelocity_zero theta z)
    have hAlphaC : alpha < theta.c := hbelow.trans theta.c_gt_one
    exact ⟨fun _ ↦ by simpa only [sub_add_cancel, zero_add] using hmean,
      fun h ↦ (not_lt_of_ge hAlphaC.le h).elim,
      hm.2⟩
  · rcases lt_or_gt_of_ne hC with hbelowC | haboveC
    · let eta : ℝ := min (alpha - 1) (theta.c - alpha)
      have heta : 0 < eta :=
        lt_min (sub_pos.mpr haboveOne) (sub_pos.mpr hbelowC)
      have hgap : ∀ a ∈ ({alpha} : Set ℝ), ∀ j : Fin 3, j ≠ 1 →
          eta ≤ shannonExponent theta 1 a - shannonExponent theta j a := by
        intro a ha j hj
        simp only [mem_singleton_iff] at ha
        subst a
        rcases j with ⟨j, hjlt⟩
        interval_cases j
        · simp [shannonExponent, shannonCountExponent, shannonAmplitude]
          dsimp only [eta]
          linarith [min_le_left (alpha - 1) (theta.c - alpha)]
        · exact (hj rfl).elim
        · simp [shannonExponent, shannonCountExponent, shannonAmplitude]
          dsimp only [eta]
          linarith [min_le_right (alpha - 1) (theta.c - alpha)]
      have hm := shannonDominantMomentTendsto theta z alpha 1 eta heta hgap
      have hmean := hm.1.add (tendsto_shannonBlockVelocity_one theta z)
      exact ⟨fun _ ↦ by simpa only [sub_add_cancel, zero_add] using hmean,
        fun h ↦ (not_lt_of_ge hbelowC.le h).elim,
        hm.2⟩
    · let eta : ℝ := alpha - theta.c
      have heta : 0 < eta := sub_pos.mpr haboveC
      have hgap : ∀ a ∈ ({alpha} : Set ℝ), ∀ j : Fin 3, j ≠ 2 →
          eta ≤ shannonExponent theta 2 a - shannonExponent theta j a := by
        intro a ha j hj
        simp only [mem_singleton_iff] at ha
        subst a
        rcases j with ⟨j, hjlt⟩
        interval_cases j
        · simp [shannonExponent, shannonCountExponent, shannonAmplitude]
          dsimp only [eta]
          linarith [theta.c_gt_one]
        · simp [shannonExponent, shannonCountExponent, shannonAmplitude]
          dsimp only [eta]
          linarith
        · exact (hj rfl).elim
      have hm := shannonDominantMomentTendsto theta z alpha 2 eta heta hgap
      have hmean : Tendsto (fun n ↦ shannonMean theta n z alpha) atTop
          (𝓝 z.2) := by
        have hsum := hm.1.add
          (show Tendsto (fun _ : ℕ ↦ z.2) atTop (𝓝 z.2) from tendsto_const_nhds)
        convert hsum using 1
        · funext n
          rw [shannonBlockVelocity_two]
          ring
        · ring_nf
      exact ⟨fun h ↦ (not_lt_of_ge haboveC.le h).elim, fun _ ↦ hmean, hm.2⟩

private theorem tendsto_shannonMean_one (theta : ShannonData) (z : ℝ × ℝ) :
    Tendsto (fun n ↦ shannonMean theta n z 1) atTop (𝓝 0) := by
  have hmass := (shannonLogMass theta ({z} : Set (ℝ × ℝ))
    (singleton_nonempty z) isCompact_singleton).1
  have heval := (compactUniformSingleton
    (fun n z ↦ shannonLogMassKernel theta n z 1) (fun _ ↦ 0) z).2 hmass
  simpa only [shannonLogMassKernel_one] using heval

private theorem tendsto_shannonKernels_at (theta : ShannonData)
    (z : ℝ × ℝ) (beta : Param)
    (hbetaC : beta ≠ finiteParam theta.c) :
    Tendsto (fun n ↦ shannonKOne theta n z beta) atTop
        (𝓝 (shannonPointFirst theta z beta)) ∧
      Tendsto (fun n ↦ shannonKTwo theta n z beta) atTop
        (𝓝 (shannonPointSecond theta z beta)) := by
  by_cases hbetaTop : beta = (⊤ : Param)
  · subst beta
    have hm1 := tendsto_shannonMean_one theta z
    constructor
    · have h := hm1.sub (show Tendsto (fun _ : ℕ ↦ z.2) atTop (𝓝 z.2) from
        tendsto_const_nhds)
      convert h using 1
      · funext n
        exact shannonKOne_top theta n z
      · simp only [shannonPointFirst_top, zero_sub]
    · have hsq := hm1.pow 2
      have h := (show Tendsto (fun _ : ℕ ↦ z.2 ^ 2) atTop (𝓝 (z.2 ^ 2)) from
        tendsto_const_nhds).sub hsq
      convert h using 1
      · funext n
        exact shannonKTwo_top theta n z
      · rw [shannonPointSecond_top]
        norm_num
  let alpha := ENNReal.toReal beta
  have hAlpha0 : 0 ≤ alpha := ENNReal.toReal_nonneg
  have hback : finiteParam alpha = beta := by
    simpa only [alpha, paramToReal] using finiteParam_paramToReal beta hbetaTop
  by_cases hAlphaZero : alpha = 0
  · have hbetaZero : beta = 0 := by
      rw [← hback, hAlphaZero, finiteParam_zero]
    constructor
    · simpa only [hbetaZero, shannonKOne_zero_local, shannonPointFirst_zero] using
        (show Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0) from tendsto_const_nhds)
    · simpa only [hbetaZero, shannonKTwo_zero, shannonPointSecond_zero] using
        (show Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0) from tendsto_const_nhds)
  have hAlpha : 0 < alpha := lt_of_le_of_ne hAlpha0 (Ne.symm hAlphaZero)
  by_cases hAlphaOne : alpha = 1
  · have hbetaOne : beta = 1 := by
      rw [← hback, hAlphaOne, finiteParam_one]
    rw [hbetaOne]
    obtain ⟨_lambda0, _hlambda0, _hpos, _hCtwo, hfirst, hsecond⟩ :=
      uniformShannonExpansion theta ({z} : Set (ℝ × ℝ))
        isCompact_singleton (singleton_nonempty z)
    have hfirstEval := (compactUniformSingleton
      (fun n z ↦ shannonKOne theta n z 1) (fun z ↦ z.1) z).2 hfirst
    have hsecondEval := (compactUniformSingleton
      (fun n z ↦ shannonKTwo theta n z 1) (fun _ ↦ 0) z).2 hsecond
    simpa only [shannonPointFirst_one, shannonPointSecond_one] using
      And.intro hfirstEval hsecondEval
  have hAlphaC : alpha ≠ theta.c := by
    intro h
    apply hbetaC
    rw [← hback, h]
  have hm := shannonMoments_tendsto_finite theta z hAlpha hAlphaOne hAlphaC
  have hm1 := tendsto_shannonMean_one theta z
  rcases lt_or_gt_of_ne hAlphaC with hbelowC | haboveC
  · have hmean := hm.1 hbelowC
    have hpoint := shannonPoint_finite_of_lt theta z hAlpha hAlphaOne hbelowC
    have hfirstLim : Tendsto
        (fun n ↦ singularWeight (finiteParam alpha) *
          (shannonMean theta n z alpha - shannonMean theta n z 1))
        atTop (𝓝 0) := by
      simpa only [sub_self, mul_zero] using
        tendsto_const_nhds.mul (hmean.sub hm1)
    have hsecondLim : Tendsto
        (fun n ↦ -alpha * shannonVar theta n z alpha +
          singularWeight (finiteParam alpha) *
            (shannonMean theta n z 1 ^ 2 -
              shannonMean theta n z alpha ^ 2)) atTop (𝓝 0) := by
      have hv := (show Tendsto (fun _ : ℕ ↦ -alpha) atTop (𝓝 (-alpha)) from
        tendsto_const_nhds).mul hm.2.2
      have hs := (show Tendsto
          (fun _ : ℕ ↦ singularWeight (finiteParam alpha)) atTop
            (𝓝 (singularWeight (finiteParam alpha))) from tendsto_const_nhds).mul
        ((hm1.pow 2).sub (hmean.pow 2))
      simpa only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        sub_self, add_zero] using hv.add hs
    constructor
    · convert hfirstLim using 1
      · funext n
        rw [← hback, shannonKOne_finite theta n z hAlpha hAlphaOne]
      · rw [← hback, hpoint.1]
    · convert hsecondLim using 1
      · funext n
        rw [← hback, shannonKTwo_finite theta n z hAlpha hAlphaOne]
      · rw [← hback, hpoint.2]
  · have hmean := hm.2.1 haboveC
    have hpoint := shannonPoint_finite_of_gt theta z haboveC
    have hfirstLim : Tendsto
        (fun n ↦ singularWeight (finiteParam alpha) *
          (shannonMean theta n z alpha - shannonMean theta n z 1))
        atTop (𝓝 (singularWeight (finiteParam alpha) * z.2)) := by
      simpa only [sub_zero] using tendsto_const_nhds.mul (hmean.sub hm1)
    have hsecondLim : Tendsto
        (fun n ↦ -alpha * shannonVar theta n z alpha +
          singularWeight (finiteParam alpha) *
            (shannonMean theta n z 1 ^ 2 -
              shannonMean theta n z alpha ^ 2))
        atTop (𝓝 (-singularWeight (finiteParam alpha) * z.2 ^ 2)) := by
      have hv := (show Tendsto (fun _ : ℕ ↦ -alpha) atTop (𝓝 (-alpha)) from
        tendsto_const_nhds).mul hm.2.2
      have hs := (show Tendsto
          (fun _ : ℕ ↦ singularWeight (finiteParam alpha)) atTop
            (𝓝 (singularWeight (finiteParam alpha))) from tendsto_const_nhds).mul
        ((hm1.pow 2).sub (hmean.pow 2))
      convert hv.add hs using 1
      ring
    constructor
    · convert hfirstLim using 1
      · funext n
        rw [← hback, shannonKOne_finite theta n z hAlpha hAlphaOne]
      · rw [← hback, hpoint.1]
    · convert hsecondLim using 1
      · funext n
        rw [← hback, shannonKTwo_finite theta n z hAlpha hAlphaOne]
      · rw [← hback, hpoint.2]

private theorem uniformPointError_punit
    {E : Type*} (fN : ℕ → E → ℝ) (f : E → ℝ) (n : ℕ) (e : E) :
    uniformPointError
        (fun m x (_u : PUnit) ↦ fN m x)
        (fun x (_u : PUnit) ↦ f x) n e =
      |fN n e - f e| := by
  unfold uniformPointError
  simp

private theorem uniformIntegralErrorSigned_punit
    {E : Type*} [MeasurableSpace E] (mu : SignedMeasure E)
    (fN : ℕ → E → ℝ) (f : E → ℝ) (n : ℕ) :
    uniformIntegralErrorSigned mu
        (fun m x (_u : PUnit) ↦ fN m x)
        (fun x (_u : PUnit) ↦ f x) n =
      |signedIntegral mu (fN n) - signedIntegral mu f| := by
  unfold uniformIntegralErrorSigned
  simp

/-- Scalar specialization of the signed uniform DCT. -/
private theorem signedIntegral_tendsto_of_uniform_bound
    {E : Type*} [MeasurableSpace E]
    (mu : SignedMeasure E) (fN : ℕ → E → ℝ) (f : E → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hMeasN : ∀ n, Measurable (fN n)) (hMeas : Measurable f)
    (hBoundN : ∀ n e, |fN n e| ≤ C)
    (hBound : ∀ e, |f e| ≤ C)
    (hConv : ∀ᵐ e ∂signedTV mu, Tendsto (fun n ↦ fN n e) atTop (𝓝 (f e))) :
    Tendsto (fun n ↦ signedIntegral mu (fN n)) atTop
      (𝓝 (signedIntegral mu f)) := by
  let pN : ℕ → E → PUnit.{1} → ℝ := fun n e _ ↦ fN n e
  let p : E → PUnit.{1} → ℝ := fun e _ ↦ f e
  let G : E → ℝ := fun _ ↦ 2 * C
  have hFNParts : ∀ (n : ℕ) (u : PUnit.{1}),
      Measurable (fun e ↦ pN n e u) ∧
        Integrable (fun e ↦ pN n e u) (signedPos mu) ∧
        Integrable (fun e ↦ pN n e u) (signedNeg mu) := by
    intro n u
    have hpos : Integrable (fun e ↦ pN n e u) (signedPos mu) := by
      apply (integrable_const C).mono (hMeasN n).aestronglyMeasurable
      filter_upwards [] with e
      simpa only [pN, Real.norm_eq_abs, abs_of_nonneg hC] using hBoundN n e
    have hneg : Integrable (fun e ↦ pN n e u) (signedNeg mu) := by
      apply (integrable_const C).mono (hMeasN n).aestronglyMeasurable
      filter_upwards [] with e
      simpa only [pN, Real.norm_eq_abs, abs_of_nonneg hC] using hBoundN n e
    exact ⟨by simpa only [pN] using hMeasN n, hpos, hneg⟩
  have hFParts : ∀ (u : PUnit.{1}),
      Measurable (fun e ↦ p e u) ∧
        Integrable (fun e ↦ p e u) (signedPos mu) ∧
        Integrable (fun e ↦ p e u) (signedNeg mu) := by
    intro u
    have hpos : Integrable (fun e ↦ p e u) (signedPos mu) := by
      apply (integrable_const C).mono hMeas.aestronglyMeasurable
      filter_upwards [] with e
      simpa only [p, Real.norm_eq_abs, abs_of_nonneg hC] using hBound e
    have hneg : Integrable (fun e ↦ p e u) (signedNeg mu) := by
      apply (integrable_const C).mono hMeas.aestronglyMeasurable
      filter_upwards [] with e
      simpa only [p, Real.norm_eq_abs, abs_of_nonneg hC] using hBound e
    exact ⟨by simpa only [p] using hMeas, hpos, hneg⟩
  have hBdd : ∀ (n : ℕ) (e : E), BddAbove
      {r : ℝ | ∃ u : PUnit.{1}, r = |pN n e u - p e u|} := by
    intro n e
    refine ⟨2 * C, ?_⟩
    rintro r ⟨u, rfl⟩
    calc
      |pN n e u - p e u| ≤ |pN n e u| + |p e u| := abs_sub _ _
      _ ≤ C + C := by
        simpa only [pN, p] using add_le_add (hBoundN n e) (hBound e)
      _ = 2 * C := by ring
  have hPointMeas : ∀ n : ℕ, Measurable
      (uniformPointError (E := E) (K := PUnit.{1}) pN p n) := by
    intro n
    have heq : uniformPointError (E := E) (K := PUnit.{1}) pN p n =
        fun e ↦ |fN n e - f e| := by
      funext e
      simpa only [pN, p] using uniformPointError_punit fN f n e
    rw [heq]
    simpa only [Function.comp_apply, Pi.sub_apply, Real.norm_eq_abs] using
      ((hMeasN n).sub hMeas).norm
  have hPointConv : ∀ᵐ e ∂signedTV mu,
      Tendsto (fun n ↦ uniformPointError (E := E) (K := PUnit.{1})
        pN p n e) atTop (𝓝 0) := by
    filter_upwards [hConv] with e he
    have hdiff : Tendsto (fun n ↦ fN n e - f e) atTop (𝓝 0) := by
      simpa only [sub_self] using he.sub
        (show Tendsto (fun _ : ℕ ↦ f e) atTop (𝓝 (f e)) from
          tendsto_const_nhds)
    have habs := (continuous_abs.tendsto 0).comp hdiff
    change Tendsto (fun n ↦ |fN n e - f e|) atTop (𝓝 |(0 : ℝ)|) at habs
    simpa only [pN, p, uniformPointError_punit, abs_zero] using habs
  have hG : Integrable G (signedTV mu) := integrable_const (2 * C)
  have hDom : ∀ (n : ℕ) (e : E),
      0 ≤ uniformPointError (E := E) (K := PUnit.{1}) pN p n e ∧
        uniformPointError (E := E) (K := PUnit.{1}) pN p n e ≤ G e := by
    intro n e
    rw [show uniformPointError (E := E) (K := PUnit.{1}) pN p n e =
        |fN n e - f e| by
      simpa only [pN, p] using uniformPointError_punit fN f n e]
    constructor
    · exact abs_nonneg _
    · dsimp only [G]
      exact (abs_sub _ _).trans <| by
        simpa only [two_mul] using add_le_add (hBoundN n e) (hBound e)
  have hDCT := uniformDCTSigned mu pN p G hFNParts hFParts hBdd
    hPointMeas hPointConv hG hDom
  have herr : (fun n ↦ uniformIntegralErrorSigned mu pN p n) =
      fun n ↦ |signedIntegral mu (fN n) - signedIntegral mu f| := by
    funext n
    simpa only [pN, p] using uniformIntegralErrorSigned_punit mu fN f n
  have habs : Tendsto
      (fun n ↦ |signedIntegral mu (fN n) - signedIntegral mu f|)
      atTop (𝓝 0) := by
    rw [← herr]
    exact hDCT.2
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Real.dist_eq] using habs

private theorem shannonPoint_bound_of_kernel_bound
    (theta : ShannonData) (z : ℝ × ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ n beta,
      |shannonKOne theta n z beta| ≤ C ∧
        |shannonKTwo theta n z beta| ≤ C) :
    ∀ beta,
      |shannonPointFirst theta z beta| ≤ C ∧
        |shannonPointSecond theta z beta| ≤ C := by
  intro beta
  by_cases hbetaC : beta = finiteParam theta.c
  · subst beta
    simp [shannonPointFirst, shannonPointSecond, hC]
  · have hlim := tendsto_shannonKernels_at theta z beta hbetaC
    have hfirstAbs : Tendsto
        (fun n ↦ |shannonKOne theta n z beta|) atTop
          (𝓝 |shannonPointFirst theta z beta|) :=
      (continuous_abs.tendsto _).comp hlim.1
    have hsecondAbs : Tendsto
        (fun n ↦ |shannonKTwo theta n z beta|) atTop
          (𝓝 |shannonPointSecond theta z beta|) :=
      (continuous_abs.tendsto _).comp hlim.2
    exact ⟨le_of_tendsto hfirstAbs (Eventually.of_forall fun n ↦ (hBound n beta).1),
      le_of_tendsto hsecondAbs (Eventually.of_forall fun n ↦ (hBound n beta).2)⟩

private theorem shannonSignedIntegrals_tendsto_at
    (mu : SignedMeasure Param) (theta : ShannonData) (z : ℝ × ℝ)
    (hmu_c : signedTV mu ({finiteParam theta.c} : Set Param) = 0) :
    Tendsto (fun n ↦ signedIntegral mu
        (fun beta ↦ shannonKOne theta n z beta)) atTop
        (𝓝 (shannonLimitFirst mu theta z)) ∧
      Tendsto (fun n ↦ signedIntegral mu
        (fun beta ↦ shannonKTwo theta n z beta)) atTop
        (𝓝 (shannonLimitSecond mu theta z)) := by
  obtain ⟨C, hC, hBound⟩ := exists_uniform_shannonKernel_bound_at theta z
  have hPointBound := shannonPoint_bound_of_kernel_bound theta z C hC hBound
  have hAway : ∀ᵐ beta ∂signedTV mu, beta ≠ finiteParam theta.c := by
    simpa only [mem_singleton_iff, not_false_eq_true] using
      (measure_eq_zero_iff_ae_notMem.mp hmu_c)
  have hConvFirst : ∀ᵐ beta ∂signedTV mu,
      Tendsto (fun n ↦ shannonKOne theta n z beta) atTop
        (𝓝 (shannonPointFirst theta z beta)) := by
    filter_upwards [hAway] with beta hbeta
    exact (tendsto_shannonKernels_at theta z beta hbeta).1
  have hConvSecond : ∀ᵐ beta ∂signedTV mu,
      Tendsto (fun n ↦ shannonKTwo theta n z beta) atTop
        (𝓝 (shannonPointSecond theta z beta)) := by
    filter_upwards [hAway] with beta hbeta
    exact (tendsto_shannonKernels_at theta z beta hbeta).2
  have hFirst := signedIntegral_tendsto_of_uniform_bound mu
    (fun n beta ↦ shannonKOne theta n z beta)
    (shannonPointFirst theta z) C hC
    (fun n ↦ (continuous_shannonKernels_param_local theta n z).1.measurable)
    (measurable_shannonPointFirst theta z)
    (fun n beta ↦ (hBound n beta).1)
    (fun beta ↦ (hPointBound beta).1) hConvFirst
  have hSecond := signedIntegral_tendsto_of_uniform_bound mu
    (fun n beta ↦ shannonKTwo theta n z beta)
    (shannonPointSecond theta z) C hC
    (fun n ↦ (continuous_shannonKernels_param_local theta n z).2.measurable)
    (measurable_shannonPointSecond theta z)
    (fun n beta ↦ (hBound n beta).2)
    (fun beta ↦ (hPointBound beta).2) hConvSecond
  constructor
  · simpa only [signedIntegral_shannonPointFirst] using hFirst
  · simpa only [signedIntegral_shannonPointSecond] using hSecond

private theorem shannonGKernel_tendsto_at
    (mu : SignedMeasure Param) (theta : ShannonData) (z : ℝ × ℝ)
    (hmu_c : signedTV mu ({finiteParam theta.c} : Set Param) = 0) :
    Tendsto (fun n ↦ shannonGKernel mu theta n z 1) atTop
        (𝓝 (shannonLimitFirst mu theta z)) ∧
      Tendsto (fun n ↦ shannonGKernel mu theta n z 2) atTop
        (𝓝 (shannonLimitSecond mu theta z)) := by
  have h := shannonSignedIntegrals_tendsto_at mu theta z hmu_c
  constructor
  · have heq : (fun n ↦ shannonGKernel mu theta n z 1) =
        fun n ↦ signedIntegral mu
          (fun beta ↦ shannonKOne theta n z beta) := by
      funext n
      exact (shannonKernelIntegralBridge mu theta n z).1
    rw [heq]
    exact h.1
  · have heq : (fun n ↦ shannonGKernel mu theta n z 2) =
        fun n ↦ signedIntegral mu
          (fun beta ↦ shannonKTwo theta n z beta) := by
      funext n
      exact (shannonKernelIntegralBridge mu theta n z).2.1
    rw [heq]
    exact h.2

private theorem shannonLimitFirst_basis (mu : SignedMeasure Param)
    (theta : ShannonData) (z : ℝ × ℝ) :
    shannonLimitFirst mu theta z =
      z.1 * shannonLimitFirst mu theta shannonBasisOne +
        z.2 * shannonLimitFirst mu theta shannonBasisTwo := by
  simp [shannonLimitFirst, shannonBasisOne, shannonBasisTwo]
  ring

private theorem shannonLimitSecond_basis (mu : SignedMeasure Param)
    (theta : ShannonData) (z : ℝ × ℝ) :
    shannonLimitSecond mu theta z =
      z.1 ^ 2 * shannonLimitSecond mu theta shannonBasisOne +
      z.1 * z.2 *
        (shannonLimitSecond mu theta (shannonBasisOne + shannonBasisTwo) -
          shannonLimitSecond mu theta shannonBasisOne -
          shannonLimitSecond mu theta shannonBasisTwo) +
      z.2 ^ 2 * shannonLimitSecond mu theta shannonBasisTwo := by
  simp [shannonLimitSecond, shannonBasisOne, shannonBasisTwo]
  ring

private theorem shannonGKernel_compactUniform
    (mu : SignedMeasure Param) (theta : ShannonData) (K : Set (ℝ × ℝ))
    (hmu_c : signedTV mu ({finiteParam theta.c} : Set Param) = 0)
    (hK : IsCompact K) (hK0 : K.Nonempty) :
    CompactUniformConverges K
        (fun n z ↦ shannonGKernel mu theta n z 1)
        (shannonLimitFirst mu theta) ∧
      CompactUniformConverges K
        (fun n z ↦ shannonGKernel mu theta n z 2)
        (shannonLimitSecond mu theta) := by
  obtain ⟨B, hB, hcoord⟩ := exists_compact_pair_abs_bound_local K hK
  have hOne := shannonGKernel_tendsto_at mu theta shannonBasisOne hmu_c
  have hTwo := shannonGKernel_tendsto_at mu theta shannonBasisTwo hmu_c
  have hSum := shannonGKernel_tendsto_at mu theta
    (shannonBasisOne + shannonBasisTwo) hmu_c
  have hFirstOne : Tendsto
      (fun n ↦ |shannonGKernel mu theta n shannonBasisOne 1 -
        shannonLimitFirst mu theta shannonBasisOne|) atTop (𝓝 0) := by
    have hdiff : Tendsto
        (fun n ↦ shannonGKernel mu theta n shannonBasisOne 1 -
          shannonLimitFirst mu theta shannonBasisOne) atTop (𝓝 0) := by
      simpa only [sub_self] using hOne.1.sub (show Tendsto
          (fun _ : ℕ ↦ shannonLimitFirst mu theta shannonBasisOne) atTop
            (𝓝 (shannonLimitFirst mu theta shannonBasisOne)) from
        tendsto_const_nhds)
    have habs := (continuous_abs.tendsto 0).comp hdiff
    change Tendsto
      (fun n ↦ |shannonGKernel mu theta n shannonBasisOne 1 -
        shannonLimitFirst mu theta shannonBasisOne|) atTop (𝓝 |(0 : ℝ)|) at habs
    simpa only [abs_zero] using habs
  have hFirstTwo : Tendsto
      (fun n ↦ |shannonGKernel mu theta n shannonBasisTwo 1 -
        shannonLimitFirst mu theta shannonBasisTwo|) atTop (𝓝 0) := by
    have hdiff : Tendsto
        (fun n ↦ shannonGKernel mu theta n shannonBasisTwo 1 -
          shannonLimitFirst mu theta shannonBasisTwo) atTop (𝓝 0) := by
      simpa only [sub_self] using hTwo.1.sub (show Tendsto
          (fun _ : ℕ ↦ shannonLimitFirst mu theta shannonBasisTwo) atTop
            (𝓝 (shannonLimitFirst mu theta shannonBasisTwo)) from
        tendsto_const_nhds)
    have habs := (continuous_abs.tendsto 0).comp hdiff
    change Tendsto
      (fun n ↦ |shannonGKernel mu theta n shannonBasisTwo 1 -
        shannonLimitFirst mu theta shannonBasisTwo|) atTop (𝓝 |(0 : ℝ)|) at habs
    simpa only [abs_zero] using habs
  let bFirst : ℕ → ℝ := fun n ↦ B *
    (|shannonGKernel mu theta n shannonBasisOne 1 -
        shannonLimitFirst mu theta shannonBasisOne| +
      |shannonGKernel mu theta n shannonBasisTwo 1 -
        shannonLimitFirst mu theta shannonBasisTwo|)
  have hbFirst : Tendsto bFirst atTop (𝓝 0) := by
    have hsum := hFirstOne.add hFirstTwo
    simpa only [bFirst, zero_add, mul_zero] using tendsto_const_nhds.mul hsum
  have hFirstPoint : ∀ n z, z ∈ K →
      |shannonGKernel mu theta n z 1 - shannonLimitFirst mu theta z| ≤
        bFirst n := by
    intro n z hz
    have hz1 := (hcoord z hz).1
    have hz2 := (hcoord z hz).2
    rw [shannonGKernel_one_basis, shannonLimitFirst_basis]
    calc
      |z.1 * shannonGKernel mu theta n shannonBasisOne 1 +
          z.2 * shannonGKernel mu theta n shannonBasisTwo 1 -
          (z.1 * shannonLimitFirst mu theta shannonBasisOne +
            z.2 * shannonLimitFirst mu theta shannonBasisTwo)| =
        |z.1 * (shannonGKernel mu theta n shannonBasisOne 1 -
            shannonLimitFirst mu theta shannonBasisOne) +
          z.2 * (shannonGKernel mu theta n shannonBasisTwo 1 -
            shannonLimitFirst mu theta shannonBasisTwo)| := by ring
      _ ≤ |z.1| *
            |shannonGKernel mu theta n shannonBasisOne 1 -
              shannonLimitFirst mu theta shannonBasisOne| +
          |z.2| *
            |shannonGKernel mu theta n shannonBasisTwo 1 -
              shannonLimitFirst mu theta shannonBasisTwo| := by
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
      _ ≤ B *
            |shannonGKernel mu theta n shannonBasisOne 1 -
              shannonLimitFirst mu theta shannonBasisOne| +
          B *
            |shannonGKernel mu theta n shannonBasisTwo 1 -
              shannonLimitFirst mu theta shannonBasisTwo| :=
        add_le_add
          (mul_le_mul_of_nonneg_right hz1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hz2 (abs_nonneg _))
      _ = bFirst n := by dsimp only [bFirst]; ring
  have hFirstBounds : ∀ n,
      0 ≤ compactUniformError K
          (fun m z ↦ shannonGKernel mu theta m z 1)
          (shannonLimitFirst mu theta) n ∧
        compactUniformError K
          (fun m z ↦ shannonGKernel mu theta m z 1)
          (shannonLimitFirst mu theta) n ≤ bFirst n := by
    intro n
    exact compactUniformError_bounds_of_point_bound K hK0 _ _ n _
      (hFirstPoint n)
  have hFirstCompact : CompactUniformConverges K
      (fun n z ↦ shannonGKernel mu theta n z 1)
      (shannonLimitFirst mu theta) := by
    unfold CompactUniformConverges
    apply squeeze_zero
    · exact fun n ↦ (hFirstBounds n).1
    · exact fun n ↦ (hFirstBounds n).2
    · exact hbFirst
  have hSecondOne : Tendsto
      (fun n ↦ |shannonGKernel mu theta n shannonBasisOne 2 -
        shannonLimitSecond mu theta shannonBasisOne|) atTop (𝓝 0) := by
    have hdiff : Tendsto
        (fun n ↦ shannonGKernel mu theta n shannonBasisOne 2 -
          shannonLimitSecond mu theta shannonBasisOne) atTop (𝓝 0) := by
      simpa only [sub_self] using hOne.2.sub (show Tendsto
          (fun _ : ℕ ↦ shannonLimitSecond mu theta shannonBasisOne) atTop
            (𝓝 (shannonLimitSecond mu theta shannonBasisOne)) from
        tendsto_const_nhds)
    have habs := (continuous_abs.tendsto 0).comp hdiff
    change Tendsto
      (fun n ↦ |shannonGKernel mu theta n shannonBasisOne 2 -
        shannonLimitSecond mu theta shannonBasisOne|) atTop (𝓝 |(0 : ℝ)|) at habs
    simpa only [abs_zero] using habs
  have hSecondTwo : Tendsto
      (fun n ↦ |shannonGKernel mu theta n shannonBasisTwo 2 -
        shannonLimitSecond mu theta shannonBasisTwo|) atTop (𝓝 0) := by
    have hdiff : Tendsto
        (fun n ↦ shannonGKernel mu theta n shannonBasisTwo 2 -
          shannonLimitSecond mu theta shannonBasisTwo) atTop (𝓝 0) := by
      simpa only [sub_self] using hTwo.2.sub (show Tendsto
          (fun _ : ℕ ↦ shannonLimitSecond mu theta shannonBasisTwo) atTop
            (𝓝 (shannonLimitSecond mu theta shannonBasisTwo)) from
        tendsto_const_nhds)
    have habs := (continuous_abs.tendsto 0).comp hdiff
    change Tendsto
      (fun n ↦ |shannonGKernel mu theta n shannonBasisTwo 2 -
        shannonLimitSecond mu theta shannonBasisTwo|) atTop (𝓝 |(0 : ℝ)|) at habs
    simpa only [abs_zero] using habs
  have hSecondSum : Tendsto
      (fun n ↦ |shannonGKernel mu theta n
          (shannonBasisOne + shannonBasisTwo) 2 -
        shannonLimitSecond mu theta
          (shannonBasisOne + shannonBasisTwo)|) atTop (𝓝 0) := by
    have hdiff : Tendsto
        (fun n ↦ shannonGKernel mu theta n
            (shannonBasisOne + shannonBasisTwo) 2 -
          shannonLimitSecond mu theta
            (shannonBasisOne + shannonBasisTwo)) atTop (𝓝 0) := by
      simpa only [sub_self] using hSum.2.sub (show Tendsto
          (fun _ : ℕ ↦ shannonLimitSecond mu theta
            (shannonBasisOne + shannonBasisTwo)) atTop
            (𝓝 (shannonLimitSecond mu theta
              (shannonBasisOne + shannonBasisTwo))) from tendsto_const_nhds)
    have habs := (continuous_abs.tendsto 0).comp hdiff
    change Tendsto
      (fun n ↦ |shannonGKernel mu theta n
          (shannonBasisOne + shannonBasisTwo) 2 -
        shannonLimitSecond mu theta
          (shannonBasisOne + shannonBasisTwo)|) atTop (𝓝 |(0 : ℝ)|) at habs
    simpa only [abs_zero] using habs
  let bSecond : ℕ → ℝ := fun n ↦ B ^ 2 *
    (2 * |shannonGKernel mu theta n shannonBasisOne 2 -
        shannonLimitSecond mu theta shannonBasisOne| +
      2 * |shannonGKernel mu theta n shannonBasisTwo 2 -
        shannonLimitSecond mu theta shannonBasisTwo| +
      |shannonGKernel mu theta n (shannonBasisOne + shannonBasisTwo) 2 -
        shannonLimitSecond mu theta
          (shannonBasisOne + shannonBasisTwo)|)
  have hbSecond : Tendsto bSecond atTop (𝓝 0) := by
    have hsum := ((hSecondOne.const_mul 2).add
      (hSecondTwo.const_mul 2)).add hSecondSum
    simpa only [bSecond, zero_add, add_zero, mul_zero] using
      tendsto_const_nhds.mul hsum
  have hSecondPoint : ∀ n z, z ∈ K →
      |shannonGKernel mu theta n z 2 - shannonLimitSecond mu theta z| ≤
        bSecond n := by
    intro n z hz
    have hz1 := (hcoord z hz).1
    have hz2 := (hcoord z hz).2
    have hz1sq : |z.1| ^ 2 ≤ B ^ 2 := by nlinarith [abs_nonneg z.1]
    have hz2sq : |z.2| ^ 2 ≤ B ^ 2 := by nlinarith [abs_nonneg z.2]
    have hz12 : |z.1| * |z.2| ≤ B ^ 2 := by
      calc
        |z.1| * |z.2| ≤ B * B :=
          mul_le_mul hz1 hz2 (abs_nonneg _) hB
        _ = B ^ 2 := by ring
    let ea := shannonGKernel mu theta n shannonBasisOne 2 -
      shannonLimitSecond mu theta shannonBasisOne
    let eb := shannonGKernel mu theta n shannonBasisTwo 2 -
      shannonLimitSecond mu theta shannonBasisTwo
    let ec := shannonGKernel mu theta n
        (shannonBasisOne + shannonBasisTwo) 2 -
      shannonLimitSecond mu theta
        (shannonBasisOne + shannonBasisTwo)
    have hcross : |ec - ea - eb| ≤ |ec| + |ea| + |eb| := by
      calc
        |ec - ea - eb| ≤ |ec - ea| + |eb| := abs_sub _ _
        _ ≤ (|ec| + |ea|) + |eb| :=
          add_le_add (abs_sub ec ea) le_rfl
    rw [shannonGKernel_two_basis, shannonLimitSecond_basis]
    calc
      |z.1 ^ 2 * shannonGKernel mu theta n shannonBasisOne 2 +
          z.1 * z.2 *
            (shannonGKernel mu theta n
                (shannonBasisOne + shannonBasisTwo) 2 -
              shannonGKernel mu theta n shannonBasisOne 2 -
              shannonGKernel mu theta n shannonBasisTwo 2) +
          z.2 ^ 2 * shannonGKernel mu theta n shannonBasisTwo 2 -
          (z.1 ^ 2 * shannonLimitSecond mu theta shannonBasisOne +
            z.1 * z.2 *
              (shannonLimitSecond mu theta
                  (shannonBasisOne + shannonBasisTwo) -
                shannonLimitSecond mu theta shannonBasisOne -
                shannonLimitSecond mu theta shannonBasisTwo) +
            z.2 ^ 2 * shannonLimitSecond mu theta shannonBasisTwo)| =
        |z.1 ^ 2 * ea + z.1 * z.2 * (ec - ea - eb) +
          z.2 ^ 2 * eb| := by
        dsimp only [ea, eb, ec]
        congr 1
        ring
      _ ≤
          |z.1 ^ 2 * ea| + |z.1 * z.2 * (ec - ea - eb)| +
            |z.2 ^ 2 * eb| := by
        exact (abs_add_le _ _).trans <|
          add_le_add (abs_add_le _ _) le_rfl
      _ = |z.1| ^ 2 * |ea| + (|z.1| * |z.2|) * |ec - ea - eb| +
            |z.2| ^ 2 * |eb| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_pow]
      _ ≤ B ^ 2 * |ea| + B ^ 2 * (|ec| + |ea| + |eb|) +
            B ^ 2 * |eb| := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_right hz1sq (abs_nonneg _))
            ((mul_le_mul hz12 hcross (abs_nonneg _) (sq_nonneg B))))
          (mul_le_mul_of_nonneg_right hz2sq (abs_nonneg _))
      _ = bSecond n := by
        dsimp only [bSecond, ea, eb, ec]
        ring
  have hSecondBounds : ∀ n,
      0 ≤ compactUniformError K
          (fun m z ↦ shannonGKernel mu theta m z 2)
          (shannonLimitSecond mu theta) n ∧
        compactUniformError K
          (fun m z ↦ shannonGKernel mu theta m z 2)
          (shannonLimitSecond mu theta) n ≤ bSecond n := by
    intro n
    exact compactUniformError_bounds_of_point_bound K hK0 _ _ n _
      (hSecondPoint n)
  have hSecondCompact : CompactUniformConverges K
      (fun n z ↦ shannonGKernel mu theta n z 2)
      (shannonLimitSecond mu theta) := by
    unfold CompactUniformConverges
    apply squeeze_zero
    · exact fun n ↦ (hSecondBounds n).1
    · exact fun n ↦ (hSecondBounds n).2
    · exact hbSecond
  exact ⟨hFirstCompact, hSecondCompact⟩

/-- Dedicated Shannon localization for the logarithmic and norm-free
columns.  The four clauses are, in manuscript order, logarithmic orders one
and two followed by norm-free orders one and two. -/
theorem shannonLocalization
    (mu : SignedMeasure Param) (theta : ShannonData) (K : Set (ℝ × ℝ))
    (hmu_c : signedTV mu ({finiteParam theta.c} : Set Param) = 0)
    (hK : IsCompact K) (hK0 : K.Nonempty) :
    Tendsto
        (fun n ↦ compactUniformError K
          (fun m z ↦ shannonLogKernel mu theta m z 1)
          (shannonLimitFirst mu theta) n)
        atTop (𝓝 0) ∧
      Tendsto
        (fun n ↦ compactUniformError K
          (fun m z ↦ shannonLogKernel mu theta m z 2)
          (shannonLimitSecond mu theta) n)
        atTop (𝓝 0) ∧
      Tendsto
        (fun n ↦ compactUniformError K
          (fun m z ↦ shannonGKernel mu theta m z 1)
          (shannonLimitFirst mu theta) n)
        atTop (𝓝 0) ∧
      Tendsto
        (fun n ↦ compactUniformError K
          (fun m z ↦ shannonGKernel mu theta m z 2)
          (shannonLimitSecond mu theta) n)
        atTop (𝓝 0) := by
  have hG := shannonGKernel_compactUniform mu theta K hmu_c hK hK0
  have hMass := shannonLogMass theta K hK0 hK
  have hMassOne : CompactUniformConverges K
      (fun n z ↦ shannonLogMassKernel theta n z 1) (fun _ ↦ 0) :=
    hMass.1
  have hMassTwo : CompactUniformConverges K
      (fun n z ↦ shannonLogMassKernel theta n z 2) (fun _ ↦ 0) :=
    hMass.2.1
  have hMassOneCont : ∀ n, Continuous
      (fun z : ℝ × ℝ ↦ shannonLogMassKernel theta n z 1) := by
    intro n
    have heq : (fun z : ℝ × ℝ ↦ shannonLogMassKernel theta n z 1) =
        fun z ↦ shannonMean theta n z 1 := by
      funext z
      exact shannonLogMassKernel_one theta n z
    rw [heq]
    exact continuous_shannonMean theta n 1
  have hMassTwoCont : ∀ n, Continuous
      (fun z : ℝ × ℝ ↦ shannonLogMassKernel theta n z 2) := by
    intro n
    have heq : (fun z : ℝ × ℝ ↦ shannonLogMassKernel theta n z 2) =
        fun z ↦ -(shannonMean theta n z 1) ^ 2 := by
      funext z
      exact shannonLogMassKernel_two theta n z
    rw [heq]
    exact ((continuous_shannonMean theta n 1).pow 2).neg
  have hLogOneAdd := compactUniformConverges_add K hK0 hK
    (fun n z ↦ shannonLogMassKernel theta n z 1)
    (fun n z ↦ shannonGKernel mu theta n z 1)
    (fun _ ↦ 0) (shannonLimitFirst mu theta)
    (fun n ↦ (hMassOneCont n).continuousOn)
    (fun n ↦ ((shannonKernelRegularity mu theta n).2.2.1).continuousOn)
    continuous_const.continuousOn
    (continuous_shannonLimitFirst mu theta).continuousOn hMassOne hG.1
  have hLogTwoAdd := compactUniformConverges_add K hK0 hK
    (fun n z ↦ shannonLogMassKernel theta n z 2)
    (fun n z ↦ shannonGKernel mu theta n z 2)
    (fun _ ↦ 0) (shannonLimitSecond mu theta)
    (fun n ↦ (hMassTwoCont n).continuousOn)
    (fun n ↦ ((shannonKernelRegularity mu theta n).2.2.2).continuousOn)
    continuous_const.continuousOn
    (continuous_shannonLimitSecond mu theta).continuousOn hMassTwo hG.2
  have hLogOne : CompactUniformConverges K
      (fun n z ↦ shannonLogKernel mu theta n z 1)
      (shannonLimitFirst mu theta) := by
    have heq : (fun n z ↦ shannonLogKernel mu theta n z 1) =
        fun n z ↦ shannonLogMassKernel theta n z 1 +
          shannonGKernel mu theta n z 1 := by
      funext n z
      exact (shannonKernelIntegralBridge mu theta n z).2.2.1
    rw [heq]
    simpa only [zero_add] using hLogOneAdd
  have hLogTwo : CompactUniformConverges K
      (fun n z ↦ shannonLogKernel mu theta n z 2)
      (shannonLimitSecond mu theta) := by
    have heq : (fun n z ↦ shannonLogKernel mu theta n z 2) =
        fun n z ↦ shannonLogMassKernel theta n z 2 +
          shannonGKernel mu theta n z 2 := by
      funext n z
      exact (shannonKernelIntegralBridge mu theta n z).2.2.2
    rw [heq]
    simpa only [zero_add] using hLogTwoAdd
  exact ⟨hLogOne, hLogTwo, hG.1, hG.2⟩

end ConditionalEntropy
