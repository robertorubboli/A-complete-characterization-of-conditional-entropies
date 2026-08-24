import ConditionalEntropy.EndpointParameterContinuity
import ConditionalEntropy.ShannonLocalizationTargets

/-!
# Differentiation bridges for the Shannon localization line

Joint compactified-order continuity supplies uniform bounds on a compact
positive line interval.  The Jordan signed-integral differentiation theorem
then identifies the first two derivatives with the declared endpoint-aware
entropy kernels.
-/

noncomputable section

open Filter MeasureTheory Set Metric
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

private theorem continuous_param_section
    {K : Set ℝ} {F : Param × ℝ → ℝ}
    (hF : ContinuousOn F (Set.univ ×ˢ K)) {lambda : ℝ}
    (hlambda : lambda ∈ K) :
    Continuous (fun beta : Param ↦ F (beta, lambda)) := by
  rw [← continuousOn_univ]
  apply hF.comp (continuous_id.prodMk continuous_const).continuousOn
  intro beta _
  exact ⟨Set.mem_univ beta, hlambda⟩

private theorem continuousOn_line_section
    {K : Set ℝ} {F : Param × ℝ → ℝ}
    (hF : ContinuousOn F (Set.univ ×ˢ K)) (beta : Param) :
    ContinuousOn (fun lambda : ℝ ↦ F (beta, lambda)) K := by
  apply hF.comp (continuous_const.prodMk continuous_id).continuousOn
  intro lambda hlambda
  exact ⟨Set.mem_univ beta, hlambda⟩

private theorem exists_uniform_abs_bound_prod
    {K : Set ℝ} (hK : IsCompact K) {F : Param × ℝ → ℝ}
    (hF : ContinuousOn F (Set.univ ×ˢ K)) :
    ∃ C : ℝ, ∀ beta : Param, ∀ lambda ∈ K, |F (beta, lambda)| ≤ C := by
  have hdomain : IsCompact (Set.univ ×ˢ K : Set (Param × ℝ)) :=
    isCompact_univ.prod hK
  have himage : IsCompact (F '' (Set.univ ×ˢ K)) :=
    hdomain.image_of_continuousOn hF
  obtain ⟨R, hR⟩ := himage.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨max R 0, ?_⟩
  intro beta lambda hlambda
  have hmem : F (beta, lambda) ∈ closedBall (0 : ℝ) R :=
    hR ⟨(beta, lambda), ⟨Set.mem_univ beta, hlambda⟩, rfl⟩
  have hdist : dist (F (beta, lambda)) 0 ≤ R := by
    simpa only [mem_closedBall, dist_comm] using hmem
  calc
    |F (beta, lambda)| = dist (F (beta, lambda)) 0 := by
      rw [Real.dist_eq]
      simp
    _ ≤ R := hdist
    _ ≤ max R 0 := le_max_left _ _

private theorem integrable_of_continuous_bounded_param
    (nu : Measure Param) [IsFiniteMeasure nu] (f : Param → ℝ)
    (hf : Continuous f) (C : ℝ) (hC : ∀ beta, |f beta| ≤ C) :
    Integrable f nu := by
  apply Integrable.of_bound hf.aestronglyMeasurable C
  exact ae_of_all nu fun beta ↦ by
    simpa only [Real.norm_eq_abs] using hC beta

private theorem continuousOn_signedIntegral_of_joint_bound
    (mu : SignedMeasure Param) {K U : Set ℝ} (hUK : U ⊆ K)
    {F : Param × ℝ → ℝ}
    (hF : ContinuousOn F (Set.univ ×ˢ K)) (C : ℝ)
    (hC : ∀ beta : Param, ∀ lambda ∈ K, |F (beta, lambda)| ≤ C) :
    ContinuousOn
      (fun lambda ↦ signedIntegral mu (fun beta ↦ F (beta, lambda))) U := by
  have hpos : ContinuousOn
      (fun lambda ↦ ∫ beta, F (beta, lambda) ∂signedPos mu) U := by
    apply continuousOn_of_dominated
    · intro lambda hlambda
      exact (continuous_param_section hF (hUK hlambda)).aestronglyMeasurable
    · intro lambda hlambda
      exact ae_of_all (signedPos mu) fun beta ↦ by
        simpa only [Real.norm_eq_abs] using hC beta lambda (hUK hlambda)
    · exact integrable_const C
    · exact ae_of_all (signedPos mu) fun beta ↦
        (continuousOn_line_section hF beta).mono hUK
  have hneg : ContinuousOn
      (fun lambda ↦ ∫ beta, F (beta, lambda) ∂signedNeg mu) U := by
    apply continuousOn_of_dominated
    · intro lambda hlambda
      exact (continuous_param_section hF (hUK hlambda)).aestronglyMeasurable
    · intro lambda hlambda
      exact ae_of_all (signedNeg mu) fun beta ↦ by
        simpa only [Real.norm_eq_abs] using hC beta lambda (hUK hlambda)
    · exact integrable_const C
    · exact ae_of_all (signedNeg mu) fun beta ↦
        (continuousOn_line_section hF beta).mono hUK
  unfold signedIntegral
  exact hpos.sub hneg

/-- Endpoint-uniform derivative facts for an arbitrary compactified Renyi
parameter. -/
private theorem hasDerivAt_entropyLine_param
    {I : Type*} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) {U : Set ℝ} (hU : IsOpen U)
    (hpos : ∀ lambda ∈ U, LinePositive L lambda)
    {istar : I} (hfixed : FixedMaxCoordinate L U istar)
    (beta : Param) {lambda : ℝ} (hlambda : lambda ∈ U) :
    HasDerivAt (entropyLine L beta) (entropyLineFirst L beta lambda) lambda ∧
      HasDerivAt (entropyLineFirst L beta)
        (entropyLineSecond L beta lambda) lambda := by
  by_cases htop : beta = ⊤
  · subst beta
    constructor
    · convert hasDerivAt_entropyLine_top_on L hU hfixed hlambda using 1
      exact entropyLineFirst_top_on L hU hfixed hlambda
    · convert hasDerivAt_entropyLineFirst_top_on L hU hfixed hlambda using 1
      exact entropyLineSecond_top_on L hU hfixed hlambda
  · let a : ℝ := ENNReal.toReal beta
    have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
    have hreconstruct : finiteParam a = beta := ENNReal.ofReal_toReal htop
    by_cases haZero : a = 0
    · have hbetaZero : beta = 0 := by
        rw [← hreconstruct, haZero, finiteParam_zero]
      rw [hbetaZero]
      constructor
      · convert hasDerivAt_entropyLine_zero L (hpos lambda hlambda) using 1
        exact entropyLineFirst_zero L (hpos lambda hlambda)
      · convert hasDerivAt_entropyLineFirst_zero L (hpos lambda hlambda) using 1
        exact entropyLineSecond_zero L (hpos lambda hlambda)
    · by_cases haOne : a = 1
      · have hbetaOne : beta = 1 := by
          rw [← hreconstruct, haOne, finiteParam_one]
        constructor
        · rw [hbetaOne]
          convert hasDerivAt_entropyLine_one L (hpos lambda hlambda) using 1
          exact entropyLineFirst_one L (hpos lambda hlambda)
        · rw [hbetaOne]
          convert hasDerivAt_entropyLineFirst_one L (hpos lambda hlambda) using 1
          exact entropyLineSecond_one L (hpos lambda hlambda)
      · have haPos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm haZero)
        rw [← hreconstruct]
        constructor
        · convert hasDerivAt_entropyLine_finite_on L hU hpos haPos haOne hlambda using 1
          exact entropyLineFirst_finite_on L hU hpos haPos haOne hlambda
        · convert hasDerivAt_entropyLineFirst_finite_on L hU hpos
            haPos haOne hlambda using 1
          exact entropyLineSecond_finite_on L hU hpos haPos haOne hlambda

/-- Dominated differentiation for the full Shannon line, simultaneously at
all points of one positive neighbourhood of the base point. -/
theorem shannonIntegralDerivativePackage (mu : SignedMeasure Param)
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) :
    letI := shannonIndexNonempty theta n
    ∃ epsilon : ℝ, 0 < epsilon ∧
      (∀ lambda ∈ Ioo (-epsilon) epsilon,
        LinePositive (shannonLineData theta n z) lambda) ∧
      (∀ lambda ∈ Ioo (-epsilon) epsilon,
        HasDerivAt (integratedEntropyLine mu (shannonLineData theta n z))
          (signedIntegral mu (fun beta ↦
            entropyLineFirst (shannonLineData theta n z) beta lambda)) lambda ∧
        HasDerivAt
          (fun s ↦ signedIntegral mu (fun beta ↦
            entropyLineFirst (shannonLineData theta n z) beta s))
          (signedIntegral mu (fun beta ↦
            entropyLineSecond (shannonLineData theta n z) beta lambda)) lambda) ∧
      ContinuousOn
        (fun lambda ↦ signedIntegral mu (fun beta ↦
          entropyLine (shannonLineData theta n z) beta lambda))
        (Ioo (-epsilon) epsilon) ∧
      ContinuousOn
        (fun lambda ↦ signedIntegral mu (fun beta ↦
          entropyLineFirst (shannonLineData theta n z) beta lambda))
        (Ioo (-epsilon) epsilon) ∧
      ContinuousOn
        (fun lambda ↦ signedIntegral mu (fun beta ↦
          entropyLineSecond (shannonLineData theta n z) beta lambda))
        (Ioo (-epsilon) epsilon) := by
  letI := shannonIndexNonempty theta n
  let L := shannonLineData theta n z
  let istar := shannonRepresentative theta n 2
  obtain ⟨epsilon0, hepsilon0, hfixed0⟩ :=
    exists_fixedMaxCoordinate_shannonLine theta n z
  let epsilon := epsilon0 / 2
  have hepsilon : 0 < epsilon := div_pos hepsilon0 (by norm_num)
  have hsubset : Icc (-epsilon) epsilon ⊆ Ioo (-epsilon0) epsilon0 := by
    intro lambda hlambda
    have hepslt : epsilon < epsilon0 := by
      dsimp only [epsilon]
      linarith
    exact ⟨(neg_lt_neg hepslt).trans_le hlambda.1,
      hlambda.2.trans_lt hepslt⟩
  have hfixed : FixedMaxCoordinate L (Icc (-epsilon) epsilon) istar := by
    intro lambda hlambda
    exact hfixed0 lambda (hsubset hlambda)
  have hpos : ∀ lambda ∈ Icc (-epsilon) epsilon, LinePositive L lambda := by
    intro lambda hlambda
    exact (hfixed lambda hlambda).1
  have hbundle := continuousOn_entropyLine_full_bundle L hepsilon hpos hfixed
  let k0 : ℝ → Param → ℝ := fun lambda beta ↦ entropyLine L beta lambda
  let k1 : ℝ → Param → ℝ := fun lambda beta ↦ entropyLineFirst L beta lambda
  let k2 : ℝ → Param → ℝ := fun lambda beta ↦ entropyLineSecond L beta lambda
  obtain ⟨C0, hC0⟩ := exists_uniform_abs_bound_prod isCompact_Icc hbundle.1
  obtain ⟨C1, hC1⟩ := exists_uniform_abs_bound_prod isCompact_Icc hbundle.2.1
  obtain ⟨C2, hC2⟩ := exists_uniform_abs_bound_prod isCompact_Icc hbundle.2.2
  have hk0cont : ∀ lambda ∈ Icc (-epsilon) epsilon,
      Continuous (k0 lambda) := by
    intro lambda hlambda
    exact continuous_param_section hbundle.1 hlambda
  have hk1cont : ∀ lambda ∈ Icc (-epsilon) epsilon,
      Continuous (k1 lambda) := by
    intro lambda hlambda
    exact continuous_param_section hbundle.2.1 hlambda
  have hk2cont : ∀ lambda ∈ Icc (-epsilon) epsilon,
      Continuous (k2 lambda) := by
    intro lambda hlambda
    exact continuous_param_section hbundle.2.2 hlambda
  have hIooMem (lambda : ℝ) (hlambda : lambda ∈ Ioo (-epsilon) epsilon) :
      Ioo (-epsilon) epsilon ∈ nhds lambda := isOpen_Ioo.mem_nhds hlambda
  have hposOpen : ∀ lambda ∈ Ioo (-epsilon) epsilon, LinePositive L lambda := by
    intro lambda hlambda
    exact hpos lambda ⟨le_of_lt hlambda.1, le_of_lt hlambda.2⟩
  have hfixedOpen : FixedMaxCoordinate L (Ioo (-epsilon) epsilon) istar := by
    intro lambda hlambda
    exact hfixed lambda ⟨le_of_lt hlambda.1, le_of_lt hlambda.2⟩
  have hOpenClosed : Ioo (-epsilon) epsilon ⊆ Icc (-epsilon) epsilon := by
    intro lambda hlambda
    exact ⟨le_of_lt hlambda.1, le_of_lt hlambda.2⟩
  have hcont0 : ContinuousOn
      (fun lambda ↦ signedIntegral mu (fun beta ↦ entropyLine L beta lambda))
      (Ioo (-epsilon) epsilon) :=
    continuousOn_signedIntegral_of_joint_bound mu hOpenClosed hbundle.1 C0 hC0
  have hcont1 : ContinuousOn
      (fun lambda ↦ signedIntegral mu (fun beta ↦ entropyLineFirst L beta lambda))
      (Ioo (-epsilon) epsilon) :=
    continuousOn_signedIntegral_of_joint_bound mu hOpenClosed hbundle.2.1 C1 hC1
  have hcont2 : ContinuousOn
      (fun lambda ↦ signedIntegral mu (fun beta ↦ entropyLineSecond L beta lambda))
      (Ioo (-epsilon) epsilon) :=
    continuousOn_signedIntegral_of_joint_bound mu hOpenClosed hbundle.2.2 C2 hC2
  refine ⟨epsilon, hepsilon, hposOpen, ?_, ?_, ?_, ?_⟩
  · intro lambda hlambda
    have hlambdaIcc : lambda ∈ Icc (-epsilon) epsilon :=
      ⟨le_of_lt hlambda.1, le_of_lt hlambda.2⟩
    have hk0intPosLambda : Integrable (k0 lambda) (signedPos mu) :=
      integrable_of_continuous_bounded_param (signedPos mu) (k0 lambda)
        (hk0cont lambda hlambdaIcc) C0 (fun beta ↦ hC0 beta lambda hlambdaIcc)
    have hk0intNegLambda : Integrable (k0 lambda) (signedNeg mu) :=
      integrable_of_continuous_bounded_param (signedNeg mu) (k0 lambda)
        (hk0cont lambda hlambdaIcc) C0 (fun beta ↦ hC0 beta lambda hlambdaIcc)
    have hk1intPosLambda : Integrable (k1 lambda) (signedPos mu) :=
      integrable_of_continuous_bounded_param (signedPos mu) (k1 lambda)
        (hk1cont lambda hlambdaIcc) C1 (fun beta ↦ hC1 beta lambda hlambdaIcc)
    have hk1intNegLambda : Integrable (k1 lambda) (signedNeg mu) :=
      integrable_of_continuous_bounded_param (signedNeg mu) (k1 lambda)
        (hk1cont lambda hlambdaIcc) C1 (fun beta ↦ hC1 beta lambda hlambdaIcc)
    have hdiff := signedIntegral_differentiate_twice mu
      (k₀ := k0) (k₁ := k1) (k₂ := k2)
      (x₀ := lambda) (s := Ioo (-epsilon) epsilon)
      (bound₀ := fun _ ↦ C1) (bound₁ := fun _ ↦ C2)
      (hIooMem lambda hlambda)
      (by
        filter_upwards [hIooMem lambda hlambda] with s hs
        exact (hk0cont s ⟨le_of_lt hs.1, le_of_lt hs.2⟩).stronglyMeasurable)
      (by
        filter_upwards [hIooMem lambda hlambda] with s hs
        exact (hk1cont s ⟨le_of_lt hs.1, le_of_lt hs.2⟩).stronglyMeasurable)
      hk0intPosLambda hk0intNegLambda hk1intPosLambda hk1intNegLambda
      (hk1cont lambda hlambdaIcc).stronglyMeasurable
      (hk2cont lambda hlambdaIcc).stronglyMeasurable
      (by
        intro beta s hs
        simpa only [k1, Real.norm_eq_abs] using
          hC1 beta s ⟨le_of_lt hs.1, le_of_lt hs.2⟩)
      (by
        intro beta s hs
        simpa only [k2, Real.norm_eq_abs] using
          hC2 beta s ⟨le_of_lt hs.1, le_of_lt hs.2⟩)
      (integrable_const C1) (integrable_const C1)
      (integrable_const C2) (integrable_const C2)
      (by
        intro beta s hs
        exact (hasDerivAt_entropyLine_param L isOpen_Ioo hposOpen hfixedOpen
          beta hs).1)
      (by
        intro beta s hs
        exact (hasDerivAt_entropyLine_param L isOpen_Ioo hposOpen hfixedOpen
          beta hs).2)
    change
      HasDerivAt
          (fun x ↦ signedIntegral mu (fun beta ↦
            entropyLine (shannonLineData theta n z) beta x))
          (signedIntegral mu (fun beta ↦
            entropyLineFirst (shannonLineData theta n z) beta lambda)) lambda ∧
        HasDerivAt
          (fun x ↦ signedIntegral mu (fun beta ↦
            entropyLineFirst (shannonLineData theta n z) beta x))
          (signedIntegral mu (fun beta ↦
            entropyLineSecond (shannonLineData theta n z) beta lambda)) lambda
    simpa only [L, k0, k1, k2] using hdiff
  · simpa only [L] using hcont0
  · simpa only [L] using hcont1
  · simpa only [L] using hcont2

/-- The four exact derivative--integral and logarithmic splitting identities
of the manuscript's Shannon bridge. -/
theorem shannonKernelIntegralBridge (mu : SignedMeasure Param)
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) :
    shannonGKernel mu theta n z 1 =
      signedIntegral mu (fun beta ↦ shannonKOne theta n z beta) ∧
    shannonGKernel mu theta n z 2 =
      signedIntegral mu (fun beta ↦ shannonKTwo theta n z beta) ∧
    shannonLogKernel mu theta n z 1 =
      shannonLogMassKernel theta n z 1 + shannonGKernel mu theta n z 1 ∧
    shannonLogKernel mu theta n z 2 =
      shannonLogMassKernel theta n z 2 + shannonGKernel mu theta n z 2 := by
  letI := shannonIndexNonempty theta n
  let L := shannonLineData theta n z
  obtain ⟨epsilon, hepsilon, hpos, hIntegral, _hcont0, _hcont1, _hcont2⟩ :=
    shannonIntegralDerivativePackage mu theta n z
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := by
    constructor <;> linarith
  have hsplit := signedLogPhiLineDerivativesOfIntegral mu L isOpen_Ioo hpos
    hIntegral hzero
  have hG1' : iteratedDeriv (integratedEntropyLine mu L) 1 0 =
      signedIntegral mu (fun beta ↦ entropyLineFirst L beta 0) :=
    hsplit.1.deriv
  have hG2' : iteratedDeriv (integratedEntropyLine mu L) 2 0 =
      signedIntegral mu (fun beta ↦ entropyLineSecond L beta 0) := by
    change deriv (deriv (integratedEntropyLine mu L)) 0 = _
    have hevent : deriv (integratedEntropyLine mu L) =ᶠ[nhds 0]
        fun s ↦ signedIntegral mu (fun beta ↦ entropyLineFirst L beta s) := by
      filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
      exact (hIntegral s hs).1.deriv
    exact ((hIntegral 0 hzero).2.congr_of_eventuallyEq hevent).deriv
  have hG1 : shannonGKernel mu theta n z 1 =
      signedIntegral mu (fun beta ↦ shannonKOne theta n z beta) := by
    simpa only [shannonGKernel, shannonKOne, L] using hG1'
  have hG2 : shannonGKernel mu theta n z 2 =
      signedIntegral mu (fun beta ↦ shannonKTwo theta n z beta) := by
    simpa only [shannonGKernel, shannonKTwo, L] using hG2'
  refine ⟨hG1, hG2, ?_, ?_⟩
  · unfold shannonLogKernel shannonLogMassKernel
    change iteratedDeriv (signedLogPhiLine mu L) 1 0 =
      deriv (fun s ↦ Real.log (lineMass L s)) 0 +
        iteratedDeriv (integratedEntropyLine mu L) 1 0
    rw [hG1']
    exact hsplit.2.2.1
  · unfold shannonLogKernel shannonLogMassKernel
    change iteratedDeriv (signedLogPhiLine mu L) 2 0 =
      secondDeriv (fun s ↦ Real.log (lineMass L s)) 0 +
        iteratedDeriv (integratedEntropyLine mu L) 2 0
    rw [hG2']
    exact hsplit.2.2.2

end ConditionalEntropy
