import ConditionalEntropy.BlockLocalization
import ConditionalEntropy.EndpointParameterContinuity
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Dependency-clean block-localization interfaces

This file closes the analytic interface between the uniform block-kernel
limit and the two- and three-block polynomials.  In particular, all
differentiation under the signed parameter integral is derived from compact
joint continuity; no unproved project-level postulate is used.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology ContDiff

namespace ConditionalEntropy

private theorem hasDerivAt_entropyLine_param
    {I : Type*} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) {U : Set ℝ} (hU : IsOpen U)
    (hpos : ∀ lambda ∈ U, LinePositive L lambda)
    {istar : I} (hfixed : FixedMaxCoordinate L U istar)
    (beta : Param) {lambda : ℝ} (hlambda : lambda ∈ U) :
    HasDerivAt (entropyLine L beta)
      (entropyLineFirst L beta lambda) lambda := by
  by_cases htop : beta = ⊤
  · subst beta
    convert hasDerivAt_entropyLine_top_on L hU hfixed hlambda using 1
    exact entropyLineFirst_top_on L hU hfixed hlambda
  let alpha : ℝ := ENNReal.toReal beta
  have hback : finiteParam alpha = beta := by
    simpa only [alpha, paramToReal] using finiteParam_paramToReal beta htop
  have halpha0 : 0 ≤ alpha := ENNReal.toReal_nonneg
  by_cases hzero : alpha = 0
  · rw [← hback, hzero, finiteParam_zero]
    convert hasDerivAt_entropyLine_zero L (hpos lambda hlambda) using 1
    exact entropyLineFirst_zero L (hpos lambda hlambda)
  by_cases hone : alpha = 1
  · rw [← hback, hone, finiteParam_one]
    convert hasDerivAt_entropyLine_one L (hpos lambda hlambda) using 1
    exact entropyLineFirst_one L (hpos lambda hlambda)
  rw [← hback]
  convert hasDerivAt_entropyLine_finite_on L hU hpos
    (lt_of_le_of_ne halpha0 (Ne.symm hzero)) hone hlambda using 1
  exact entropyLineFirst_finite_on L hU hpos
    (lt_of_le_of_ne halpha0 (Ne.symm hzero)) hone hlambda

private theorem hasDerivAt_entropyLineFirst_param
    {I : Type*} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) {U : Set ℝ} (hU : IsOpen U)
    (hpos : ∀ lambda ∈ U, LinePositive L lambda)
    {istar : I} (hfixed : FixedMaxCoordinate L U istar)
    (beta : Param) {lambda : ℝ} (hlambda : lambda ∈ U) :
    HasDerivAt (entropyLineFirst L beta)
      (entropyLineSecond L beta lambda) lambda := by
  by_cases htop : beta = ⊤
  · subst beta
    convert hasDerivAt_entropyLineFirst_top_on L hU hfixed hlambda using 1
    exact entropyLineSecond_top_on L hU hfixed hlambda
  let alpha : ℝ := ENNReal.toReal beta
  have hback : finiteParam alpha = beta := by
    simpa only [alpha, paramToReal] using finiteParam_paramToReal beta htop
  have halpha0 : 0 ≤ alpha := ENNReal.toReal_nonneg
  by_cases hzero : alpha = 0
  · rw [← hback, hzero, finiteParam_zero]
    convert hasDerivAt_entropyLineFirst_zero L (hpos lambda hlambda) using 1
    exact entropyLineSecond_zero L (hpos lambda hlambda)
  by_cases hone : alpha = 1
  · rw [← hback, hone, finiteParam_one]
    convert hasDerivAt_entropyLineFirst_one L (hpos lambda hlambda) using 1
    exact entropyLineSecond_one L (hpos lambda hlambda)
  rw [← hback]
  convert hasDerivAt_entropyLineFirst_finite_on L hU hpos
    (lt_of_le_of_ne halpha0 (Ne.symm hzero)) hone hlambda using 1
  exact entropyLineSecond_finite_on L hU hpos
    (lt_of_le_of_ne halpha0 (Ne.symm hzero)) hone hlambda

private theorem continuous_slice_of_bundle
    {delta : ℝ}
    {f : Param × ℝ → ℝ}
    (hf : ContinuousOn f (Set.univ ×ˢ Icc (-delta) delta))
    {lambda : ℝ} (hlambda : lambda ∈ Icc (-delta) delta) :
    Continuous (fun beta : Param => f (beta, lambda)) := by
  exact hf.comp_continuous (continuous_id.prodMk continuous_const)
    (fun beta => ⟨Set.mem_univ beta, hlambda⟩)

private theorem continuousOn_line_slice_of_bundle
    {delta : ℝ} {f : Param × ℝ → ℝ}
    (hf : ContinuousOn f (Set.univ ×ˢ Icc (-delta) delta))
    (beta : Param) :
    ContinuousOn (fun lambda : ℝ => f (beta, lambda))
      (Icc (-delta) delta) := by
  exact hf.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun lambda hlambda => ⟨Set.mem_univ beta, hlambda⟩)

private theorem continuousOn_signedIntegral_of_bundle
    (mu : SignedMeasure Param) {delta : ℝ} {f : Param × ℝ → ℝ}
    (hf : ContinuousOn f (Set.univ ×ˢ Icc (-delta) delta))
    (C : ℝ)
    (hC : ∀ beta : Param, ∀ lambda ∈ Icc (-delta) delta,
      |f (beta, lambda)| ≤ C) :
    ContinuousOn (fun lambda => signedIntegral mu (fun beta => f (beta, lambda)))
      (Ioo (-delta) delta) := by
  have hsub : Ioo (-delta) delta ⊆ Icc (-delta) delta := by
    intro lambda hlambda
    exact ⟨hlambda.1.le, hlambda.2.le⟩
  have hpos : ContinuousOn
      (fun lambda => ∫ beta, f (beta, lambda) ∂signedPos mu)
      (Ioo (-delta) delta) := by
    apply continuousOn_of_dominated
    · intro lambda hlambda
      exact (continuous_slice_of_bundle hf (hsub hlambda)).aestronglyMeasurable
    · intro lambda hlambda
      exact ae_of_all (signedPos mu) fun beta => by
        simpa only [Real.norm_eq_abs] using hC beta lambda (hsub hlambda)
    · exact integrable_const C
    · exact ae_of_all (signedPos mu) fun beta =>
        (continuousOn_line_slice_of_bundle hf beta).mono hsub
  have hneg : ContinuousOn
      (fun lambda => ∫ beta, f (beta, lambda) ∂signedNeg mu)
      (Ioo (-delta) delta) := by
    apply continuousOn_of_dominated
    · intro lambda hlambda
      exact (continuous_slice_of_bundle hf (hsub hlambda)).aestronglyMeasurable
    · intro lambda hlambda
      exact ae_of_all (signedNeg mu) fun beta => by
        simpa only [Real.norm_eq_abs] using hC beta lambda (hsub hlambda)
    · exact integrable_const C
    · exact ae_of_all (signedNeg mu) fun beta =>
        (continuousOn_line_slice_of_bundle hf beta).mono hsub
  unfold signedIntegral
  exact hpos.sub hneg

private theorem contDiffOn_two_of_derivative_chain
    {U : Set ℝ} (hU : IsOpen U) {f f1 f2 : ℝ → ℝ}
    (h0 : ∀ x ∈ U, HasDerivAt f (f1 x) x)
    (h1 : ∀ x ∈ U, HasDerivAt f1 (f2 x) x)
    (h2 : ContinuousOn f2 U) : ContDiffOn ℝ 2 f U := by
  have hf1 : ContDiffOn ℝ 1 f1 U := by
    rw [contDiffOn_one_iff_derivWithin hU.uniqueDiffOn]
    refine ⟨fun x hx => (h1 x hx).differentiableAt.differentiableWithinAt, ?_⟩
    exact h2.congr fun x hx => by
      rw [derivWithin_of_isOpen hU hx]
      exact (h1 x hx).deriv
  rw [show (2 : ℕ∞ω) = 1 + 1 by rfl,
    contDiffOn_succ_iff_deriv_of_isOpen hU]
  refine ⟨fun x hx => (h0 x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro h
    simp at h
  · exact hf1.congr fun x hx => (h0 x hx).deriv

private theorem iteratedDeriv_eq_of_eqOn_open_two
    {f g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U)
    (hfg : Set.EqOn f g U) (q : ℕ) (hq : q ≤ 2) :
    iteratedDeriv f q x = iteratedDeriv g q x := by
  interval_cases q
  · simp only [iteratedDeriv_zero]
    exact hfg hx
  · change deriv f x = deriv g x
    exact Filter.EventuallyEq.deriv_eq
      (eventuallyEq_of_mem (hU.mem_nhds hx) hfg)
  · change deriv (deriv f) x = deriv (deriv g) x
    have hderiv : deriv f =ᶠ[nhds x] deriv g := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact Filter.EventuallyEq.deriv_eq
        (eventuallyEq_of_mem (hU.mem_nhds hy) hfg)
    exact Filter.EventuallyEq.deriv_eq hderiv

set_option maxHeartbeats 1000000 in
-- The compactified endpoint bundle and two signed dominated differentiations elaborate deeply.
private theorem blockSignedDifferentiation
    {J : ℕ} (B : BlockData J) (mu : SignedMeasure Param)
    (n : ℕ) (u : Fin (J + 1) → ℝ)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop) :
    letI := blockCarrierNonempty B n
    let L := blockLineData B n u
    (Integrable (fun beta => entropyLineFirst L beta 0) (signedPos mu) ∧
      Integrable (fun beta => entropyLineFirst L beta 0) (signedNeg mu)) ∧
    (Integrable (fun beta => entropyLineSecond L beta 0) (signedPos mu) ∧
      Integrable (fun beta => entropyLineSecond L beta 0) (signedNeg mu)) ∧
    HasDerivAt (integratedEntropyLine mu L)
      (signedIntegral mu (fun beta => entropyLineFirst L beta 0)) 0 ∧
    HasDerivAt (deriv (integratedEntropyLine mu L))
      (signedIntegral mu (fun beta => entropyLineSecond L beta 0)) 0 ∧
    iteratedDeriv (signedLogPhiLine mu L) 1 0 =
      deriv (fun s => Real.log (lineMass L s)) 0 +
        signedIntegral mu (fun beta => entropyLineFirst L beta 0) ∧
    iteratedDeriv (signedLogPhiLine mu L) 2 0 =
      secondDeriv (fun s => Real.log (lineMass L s)) 0 +
        signedIntegral mu (fun beta => entropyLineSecond L beta 0) ∧
    ∃ epsilon : ℝ, 0 < epsilon ∧
      (∀ lambda ∈ Ioo (-epsilon) epsilon, LinePositive L lambda) ∧
      (∀ lambda ∈ Ioo (-epsilon) epsilon,
        HasDerivAt (integratedEntropyLine mu L)
            (signedIntegral mu (fun beta => entropyLineFirst L beta lambda)) lambda ∧
          HasDerivAt
            (fun s => signedIntegral mu (fun beta => entropyLineFirst L beta s))
            (signedIntegral mu (fun beta => entropyLineSecond L beta lambda)) lambda) ∧
      ContinuousOn
        (fun lambda => signedIntegral mu (fun beta => entropyLineSecond L beta lambda))
        (Ioo (-epsilon) epsilon) := by
  letI := blockCarrierNonempty B n
  let L := blockLineData B n u
  let istar : BlockCarrier B n :=
    ⟨jTop, ⟨0, blockCount_pos B n jTop⟩⟩
  obtain ⟨epsilon, hepsilon, hfixedOpen⟩ :=
    exists_fixedMaxCoordinate_blockLine B jTop hTop n u
  let delta := epsilon / 2
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hclosedSub : Icc (-delta) delta ⊆ Ioo (-epsilon) epsilon := by
    intro lambda hlambda
    dsimp only [delta] at hlambda
    constructor <;> linarith [hlambda.1, hlambda.2]
  have hfixedClosed : FixedMaxCoordinate L (Icc (-delta) delta) istar := by
    intro lambda hlambda
    exact hfixedOpen lambda (hclosedSub hlambda)
  have hposClosed : ∀ lambda ∈ Icc (-delta) delta, LinePositive L lambda :=
    fun lambda hlambda => (hfixedClosed lambda hlambda).1
  have hbundle := continuousOn_entropyLine_full_bundle L hdelta hposClosed hfixedClosed
  let S : Set (Param × ℝ) := Set.univ ×ˢ Icc (-delta) delta
  have hScompact : IsCompact S := isCompact_univ.prod isCompact_Icc
  obtain ⟨C0, hC0⟩ := hScompact.exists_bound_of_continuousOn hbundle.1
  obtain ⟨C1, hC1⟩ := hScompact.exists_bound_of_continuousOn hbundle.2.1
  obtain ⟨C2, hC2⟩ := hScompact.exists_bound_of_continuousOn hbundle.2.2
  have hzeroClosed : (0 : ℝ) ∈ Icc (-delta) delta := by constructor <;> linarith
  have hzeroOpen : (0 : ℝ) ∈ Ioo (-delta) delta := by constructor <;> linarith
  have hslice0 : Continuous (fun beta : Param => entropyLine L beta 0) :=
    continuous_slice_of_bundle hbundle.1 hzeroClosed
  have hslice1 : Continuous (fun beta : Param => entropyLineFirst L beta 0) :=
    continuous_slice_of_bundle hbundle.2.1 hzeroClosed
  have hslice2 : Continuous (fun beta : Param => entropyLineSecond L beta 0) :=
    continuous_slice_of_bundle hbundle.2.2 hzeroClosed
  have hint0Pos : Integrable (fun beta => entropyLine L beta 0) (signedPos mu) := by
    apply (integrable_const C0).mono hslice0.aestronglyMeasurable
    filter_upwards [] with beta
    exact (hC0 (beta, 0) ⟨Set.mem_univ beta, hzeroClosed⟩).trans
      (le_abs_self C0)
  have hint0Neg : Integrable (fun beta => entropyLine L beta 0) (signedNeg mu) := by
    apply (integrable_const C0).mono hslice0.aestronglyMeasurable
    filter_upwards [] with beta
    exact (hC0 (beta, 0) ⟨Set.mem_univ beta, hzeroClosed⟩).trans
      (le_abs_self C0)
  have hint1Pos : Integrable (fun beta => entropyLineFirst L beta 0) (signedPos mu) := by
    apply (integrable_const C1).mono hslice1.aestronglyMeasurable
    filter_upwards [] with beta
    exact (hC1 (beta, 0) ⟨Set.mem_univ beta, hzeroClosed⟩).trans
      (le_abs_self C1)
  have hint1Neg : Integrable (fun beta => entropyLineFirst L beta 0) (signedNeg mu) := by
    apply (integrable_const C1).mono hslice1.aestronglyMeasurable
    filter_upwards [] with beta
    exact (hC1 (beta, 0) ⟨Set.mem_univ beta, hzeroClosed⟩).trans
      (le_abs_self C1)
  have hint2Pos : Integrable (fun beta => entropyLineSecond L beta 0) (signedPos mu) := by
    apply (integrable_const C2).mono hslice2.aestronglyMeasurable
    filter_upwards [] with beta
    exact (hC2 (beta, 0) ⟨Set.mem_univ beta, hzeroClosed⟩).trans
      (le_abs_self C2)
  have hint2Neg : Integrable (fun beta => entropyLineSecond L beta 0) (signedNeg mu) := by
    apply (integrable_const C2).mono hslice2.aestronglyMeasurable
    filter_upwards [] with beta
    exact (hC2 (beta, 0) ⟨Set.mem_univ beta, hzeroClosed⟩).trans
      (le_abs_self C2)
  have hopenMem : Ioo (-delta) delta ∈ nhds (0 : ℝ) :=
    isOpen_Ioo.mem_nhds hzeroOpen
  have hIntegral : ∀ lambda ∈ Ioo (-delta) delta,
      HasDerivAt (integratedEntropyLine mu L)
          (signedIntegral mu (fun beta => entropyLineFirst L beta lambda)) lambda ∧
        HasDerivAt
          (fun s => signedIntegral mu (fun beta => entropyLineFirst L beta s))
          (signedIntegral mu (fun beta => entropyLineSecond L beta lambda)) lambda := by
    intro lambda hlambda
    have hslice0lambda : Continuous (fun beta : Param => entropyLine L beta lambda) :=
      continuous_slice_of_bundle hbundle.1 ⟨hlambda.1.le, hlambda.2.le⟩
    have hslice1lambda : Continuous
        (fun beta : Param => entropyLineFirst L beta lambda) :=
      continuous_slice_of_bundle hbundle.2.1 ⟨hlambda.1.le, hlambda.2.le⟩
    have hslice2lambda : Continuous
        (fun beta : Param => entropyLineSecond L beta lambda) :=
      continuous_slice_of_bundle hbundle.2.2 ⟨hlambda.1.le, hlambda.2.le⟩
    have hstrong0lambda : ∀ᶠ x in nhds lambda,
        StronglyMeasurable (fun beta => entropyLine L beta x) := by
      filter_upwards [isOpen_Ioo.mem_nhds hlambda] with x hx
      exact (continuous_slice_of_bundle hbundle.1
        ⟨hx.1.le, hx.2.le⟩).stronglyMeasurable
    have hstrong1lambda : ∀ᶠ x in nhds lambda,
        StronglyMeasurable (fun beta => entropyLineFirst L beta x) := by
      filter_upwards [isOpen_Ioo.mem_nhds hlambda] with x hx
      exact (continuous_slice_of_bundle hbundle.2.1
        ⟨hx.1.le, hx.2.le⟩).stronglyMeasurable
    have hint0lambdaPos : Integrable (fun beta => entropyLine L beta lambda)
        (signedPos mu) := by
      apply (integrable_const C0).mono hslice0lambda.aestronglyMeasurable
      filter_upwards [] with beta
      exact (hC0 (beta, lambda)
        ⟨Set.mem_univ beta, ⟨hlambda.1.le, hlambda.2.le⟩⟩).trans
        (le_abs_self C0)
    have hint0lambdaNeg : Integrable (fun beta => entropyLine L beta lambda)
        (signedNeg mu) := by
      apply (integrable_const C0).mono hslice0lambda.aestronglyMeasurable
      filter_upwards [] with beta
      exact (hC0 (beta, lambda)
        ⟨Set.mem_univ beta, ⟨hlambda.1.le, hlambda.2.le⟩⟩).trans
        (le_abs_self C0)
    have hint1lambdaPos : Integrable
        (fun beta => entropyLineFirst L beta lambda) (signedPos mu) := by
      apply (integrable_const C1).mono hslice1lambda.aestronglyMeasurable
      filter_upwards [] with beta
      exact (hC1 (beta, lambda)
        ⟨Set.mem_univ beta, ⟨hlambda.1.le, hlambda.2.le⟩⟩).trans
        (le_abs_self C1)
    have hint1lambdaNeg : Integrable
        (fun beta => entropyLineFirst L beta lambda) (signedNeg mu) := by
      apply (integrable_const C1).mono hslice1lambda.aestronglyMeasurable
      filter_upwards [] with beta
      exact (hC1 (beta, lambda)
        ⟨Set.mem_univ beta, ⟨hlambda.1.le, hlambda.2.le⟩⟩).trans
        (le_abs_self C1)
    exact signedIntegral_differentiate_twice
      (E := Param) (k₀ := fun x beta => entropyLine L beta x)
      (k₁ := fun x beta => entropyLineFirst L beta x)
      (k₂ := fun x beta => entropyLineSecond L beta x)
      (x₀ := lambda) (s := Ioo (-delta) delta)
      (bound₀ := fun _ => C1) (bound₁ := fun _ => C2) mu
      (isOpen_Ioo.mem_nhds hlambda) hstrong0lambda hstrong1lambda
      hint0lambdaPos hint0lambdaNeg hint1lambdaPos hint1lambdaNeg
      hslice1lambda.stronglyMeasurable hslice2lambda.stronglyMeasurable
      (fun beta x hx => hC1 (beta, x)
        ⟨Set.mem_univ beta, ⟨hx.1.le, hx.2.le⟩⟩)
      (fun beta x hx => hC2 (beta, x)
        ⟨Set.mem_univ beta, ⟨hx.1.le, hx.2.le⟩⟩)
      (integrable_const C1) (integrable_const C1)
      (integrable_const C2) (integrable_const C2)
      (fun beta x hx => hasDerivAt_entropyLine_param L isOpen_Ioo
        (fun y hy => (hfixedClosed y ⟨hy.1.le, hy.2.le⟩).1)
        (fun y hy => hfixedClosed y ⟨hy.1.le, hy.2.le⟩) beta hx)
      (fun beta x hx => hasDerivAt_entropyLineFirst_param L isOpen_Ioo
        (fun y hy => (hfixedClosed y ⟨hy.1.le, hy.2.le⟩).1)
        (fun y hy => hfixedClosed y ⟨hy.1.le, hy.2.le⟩) beta hx)
  have hbase := hIntegral 0 hzeroOpen
  have hderivEventually : deriv (integratedEntropyLine mu L) =ᶠ[nhds 0]
      fun lambda => signedIntegral mu (fun beta => entropyLineFirst L beta lambda) := by
    filter_upwards [hopenMem] with lambda hlambda
    exact (hIntegral lambda hlambda).1.deriv
  have hsecond : HasDerivAt (deriv (integratedEntropyLine mu L))
      (signedIntegral mu (fun beta => entropyLineSecond L beta 0)) 0 :=
    hbase.2.congr_of_eventuallyEq hderivEventually
  have hlog := signedLogPhiLineDerivativesOfIntegral mu L isOpen_Ioo
    (fun lambda hlambda => (hfixedClosed lambda
      ⟨hlambda.1.le, hlambda.2.le⟩).1) hIntegral hzeroOpen
  have hcont2 : ContinuousOn
      (fun lambda => signedIntegral mu (fun beta => entropyLineSecond L beta lambda))
      (Ioo (-delta) delta) :=
    continuousOn_signedIntegral_of_bundle mu hbundle.2.2 C2
      (fun beta lambda hlambda => hC2 (beta, lambda)
        ⟨Set.mem_univ beta, hlambda⟩)
  exact ⟨⟨hint1Pos, hint1Neg⟩, ⟨hint2Pos, hint2Neg⟩,
    hbase.1, hsecond, hlog.2.2.1, hlog.2.2.2,
    ⟨delta, hdelta,
      (fun lambda hlambda => hposClosed lambda ⟨hlambda.1.le, hlambda.2.le⟩),
      hIntegral, hcont2⟩⟩

/-- Exact block curve--kernel bridge through derivative order two. -/
theorem blockCurveKernelBridge {J : ℕ} (B : BlockData J)
    (mu : SignedMeasure Param) (n : ℕ) (u : Fin (J + 1) → ℝ)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      (∀ lambda ∈ Ioo (-epsilon) epsilon,
        LinePositive (blockLineData B n u) lambda) ∧
      0 < blockPhiCurve mu B n u 0 ∧
      ContDiffOn ℝ 2 (fun lambda => blockPhiCurve mu B n u lambda)
        (Ioo (-epsilon) epsilon) ∧
      ContDiffOn ℝ 2 (blockGCurve mu B n u)
        (Ioo (-epsilon) epsilon) ∧
      (∀ q : ℕ, q ≤ 2 →
        iteratedDeriv
          (fun lambda => Real.log (blockPhiCurve mu B n u lambda)) q 0 =
            blockLogKernel mu B n u q) ∧
      (∀ q : ℕ, q ≤ 2 →
        iteratedDeriv (blockGCurve mu B n u) q 0 =
          blockGKernel mu B n u q) := by
  letI := blockCarrierNonempty B n
  let L := blockLineData B n u
  have H := blockSignedDifferentiation B mu n u jTop hTop
  obtain ⟨epsilon, hepsilon, hpos, hIntegral, hcont2⟩ :=
    H.2.2.2.2.2.2
  let U : Set ℝ := Ioo (-epsilon) epsilon
  let f0 : ℝ → ℝ := fun lambda =>
    signedIntegral mu (fun beta => entropyLine L beta lambda)
  let f1 : ℝ → ℝ := fun lambda =>
    signedIntegral mu (fun beta => entropyLineFirst L beta lambda)
  let f2 : ℝ → ℝ := fun lambda =>
    signedIntegral mu (fun beta => entropyLineSecond L beta lambda)
  have hzero : (0 : ℝ) ∈ U := by
    dsimp only [U]
    constructor <;> linarith
  have hderiv0 : ∀ lambda ∈ U, HasDerivAt f0 (f1 lambda) lambda := by
    intro lambda hlambda
    have h := (hIntegral lambda hlambda).1
    change HasDerivAt
      (fun x => signedIntegral mu (fun beta =>
        entropyLine (blockLineData B n u) beta x))
      (signedIntegral mu (fun beta =>
        entropyLineFirst (blockLineData B n u) beta lambda)) lambda at h
    simpa only [f0, f1, L] using h
  have hderiv1 : ∀ lambda ∈ U, HasDerivAt f1 (f2 lambda) lambda := by
    intro lambda hlambda
    simpa only [f1, f2] using (hIntegral lambda hlambda).2
  have hf2cont : ContinuousOn f2 U := by
    simpa only [f2, U] using hcont2
  have hf0cd : ContDiffOn ℝ 2 f0 U :=
    contDiffOn_two_of_derivative_chain isOpen_Ioo hderiv0 hderiv1 hf2cont
  have hGEq : Set.EqOn (blockGCurve mu B n u) f0 U := by
    intro lambda hlambda
    simpa only [f0, L, integratedEntropyLine] using
      blockGCurve_of_positive mu B n u (hpos lambda hlambda)
  have hGcd : ContDiffOn ℝ 2 (blockGCurve mu B n u) U :=
    hf0cd.congr fun lambda hlambda => hGEq hlambda
  have hmassCd : ContDiffOn ℝ 2 (lineMass L) U := by
    unfold lineMass lineRaw
    fun_prop
  have hlogMassCd : ContDiffOn ℝ 2
      (fun lambda => Real.log (lineMass L lambda)) U :=
    hmassCd.log fun lambda hlambda =>
      (lineMass_pos L (hpos lambda hlambda)).ne'
  have hsignedLogCd : ContDiffOn ℝ 2 (signedLogPhiLine mu L) U := by
    change ContDiffOn ℝ 2
      ((fun lambda => Real.log (lineMass L lambda)) + f0) U
    exact hlogMassCd.add hf0cd
  have hexpCd : ContDiffOn ℝ 2
      (fun lambda => Real.exp (signedLogPhiLine mu L lambda)) U :=
    hsignedLogCd.exp
  have hPhiEq : Set.EqOn (fun lambda => blockPhiCurve mu B n u lambda)
      (fun lambda => Real.exp (signedLogPhiLine mu L lambda)) U := by
    intro lambda hlambda
    have hphi := blockPhiCurve_pos_of_positive mu B n u (hpos lambda hlambda)
    calc
      blockPhiCurve mu B n u lambda =
          Real.exp (Real.log (blockPhiCurve mu B n u lambda)) :=
        (Real.exp_log hphi).symm
      _ = Real.exp (signedLogPhiLine mu L lambda) := by
        rw [log_blockPhiCurve_of_positive mu B n u (hpos lambda hlambda)]
  have hPhiCd : ContDiffOn ℝ 2
      (fun lambda => blockPhiCurve mu B n u lambda) U :=
    hexpCd.congr fun lambda hlambda => hPhiEq hlambda
  have hLogEq : Set.EqOn
      (fun lambda => Real.log (blockPhiCurve mu B n u lambda))
      (signedLogPhiLine mu L) U := by
    intro lambda hlambda
    exact log_blockPhiCurve_of_positive mu B n u (hpos lambda hlambda)
  refine ⟨epsilon, hepsilon, hpos, blockPhiCurve_zero_pos mu B n u,
    ?_, ?_, ?_, ?_⟩
  · simpa only [U] using hPhiCd
  · simpa only [U] using hGcd
  · intro q hq
    have hqeq := iteratedDeriv_eq_of_eqOn_open_two
      isOpen_Ioo hzero hLogEq q hq
    simpa only [blockLogKernel, L] using hqeq
  · intro q hq
    have hqeq := iteratedDeriv_eq_of_eqOn_open_two
      isOpen_Ioo hzero hGEq q hq
    unfold blockGKernel
    change iteratedDeriv (blockGCurve mu B n u) q 0 =
      iteratedDeriv
        (fun lambda => signedIntegral mu (fun beta =>
          entropyLine (blockLineData B n u) beta lambda)) q 0
    simpa only [f0, L] using hqeq

/-- The norm-free block derivatives are exactly the signed integrals of the
first two entropy-line kernels. -/
theorem blockGKernelIntegralBridge {J : ℕ} (mu : SignedMeasure Param)
    (B : BlockData J) (n : ℕ) (u : Fin (J + 1) → ℝ)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop) :
    blockGKernel mu B n u 1 =
        signedIntegral mu (fun beta => blockKernelFirst B n u beta) ∧
      blockGKernel mu B n u 2 =
        signedIntegral mu (fun beta => blockKernelSecond B n u beta) := by
  letI := blockCarrierNonempty B n
  have H := blockSignedDifferentiation B mu n u jTop hTop
  constructor
  · exact H.2.2.1.deriv
  · exact H.2.2.2.1.deriv

private def blockMeanLinear {J : ℕ} (B : BlockData J) (n : ℕ)
    (alpha : ℝ) : (Fin (J + 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun := blockEscortMean B n alpha
  map_add' u v := by
    simp only [blockEscortMean, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    simp only [blockEscortMean, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

@[simp] private theorem blockMeanLinear_apply {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) (u : Fin (J + 1) → ℝ) :
    blockMeanLinear B n alpha u = blockEscortMean B n alpha u := rfl

private def blockOrderSlopeLinear {J : ℕ} (B : BlockData J) (n : ℕ) :
    (Fin (J + 1) → ℝ) →ₗ[ℝ] ℝ :=
  ∑ j, (deriv (fun s => blockEscort B n j s) 1) •
    LinearMap.proj j

@[simp] private theorem blockOrderSlopeLinear_apply {J : ℕ}
    (B : BlockData J) (n : ℕ) (u : Fin (J + 1) → ℝ) :
    blockOrderSlopeLinear B n u =
      ∑ j, deriv (fun s => blockEscort B n j s) 1 * u j := by
  simp [blockOrderSlopeLinear]

private def blockFirstLinear {J : ℕ} (B : BlockData J)
    (jTop : Fin (J + 1)) (n : ℕ) (beta : Param) :
    (Fin (J + 1) → ℝ) →ₗ[ℝ] ℝ :=
  if beta = ⊤ then
    blockMeanLinear B n 1 - LinearMap.proj jTop
  else if beta = 0 then 0
  else if beta = 1 then -blockOrderSlopeLinear B n
  else
    singularWeight beta •
      (blockMeanLinear B n (ENNReal.toReal beta) - blockMeanLinear B n 1)

@[simp] private theorem blockFirstLinear_apply {J : ℕ} (B : BlockData J)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop)
    (n : ℕ) (beta : Param) (u : Fin (J + 1) → ℝ) :
    blockFirstLinear B jTop n beta u = blockKernelFirst B n u beta := by
  by_cases hbetaTop : beta = (⊤ : Param)
  · subst beta
    simp [blockFirstLinear, blockKernelFirst_top_eq B jTop hTop]
  by_cases hbetaZero : beta = (0 : Param)
  · subst beta
    letI := blockCarrierNonempty B n
    have hz : blockKernelFirst B n u 0 = 0 := by
      exact entropyLineFirst_zero (blockLineData B n u) (linePositiveZero _)
    rw [hz]
    simp [blockFirstLinear]
  by_cases hbetaOne : beta = (1 : Param)
  · subst beta
    rw [blockKernelFirst_one, deriv_blockEscortMean_order]
    simp [blockFirstLinear]
  have hrealPos : 0 < ENNReal.toReal beta :=
    ENNReal.toReal_pos hbetaZero hbetaTop
  have hrealOne : ENNReal.toReal beta ≠ 1 := by
    intro h
    have hback := finiteParam_paramToReal beta hbetaTop
    rw [show paramToReal beta hbetaTop = ENNReal.toReal beta by rfl,
      h, finiteParam_one] at hback
    exact hbetaOne hback.symm
  have hback := finiteParam_paramToReal beta hbetaTop
  rw [show paramToReal beta hbetaTop = ENNReal.toReal beta by rfl] at hback
  have hk : blockKernelFirst B n u beta =
      singularWeight beta *
        (blockEscortMean B n (ENNReal.toReal beta) u -
          blockEscortMean B n 1 u) := by
    rw [← hback, blockKernelFirst_finite B n u hrealPos hrealOne]
    simp only [finiteParam, ENNReal.toReal_ofReal hrealPos.le]
  rw [hk]
  simp only [blockFirstLinear, hbetaTop, if_false, hbetaZero, hbetaOne,
    LinearMap.smul_apply, LinearMap.sub_apply, blockMeanLinear_apply,
    smul_eq_mul]

private def blockSecondMomentQuadratic {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) : QuadraticMap ℝ (Fin (J + 1) → ℝ) ℝ :=
  ∑ j, blockEscort B n j alpha • QuadraticMap.proj j j

@[simp] private theorem blockSecondMomentQuadratic_apply {J : ℕ}
    (B : BlockData J) (n : ℕ) (alpha : ℝ)
    (u : Fin (J + 1) → ℝ) :
    blockSecondMomentQuadratic B n alpha u =
      blockEscortSecond B n alpha u := by
  simp [blockSecondMomentQuadratic, blockEscortSecond]
  ring

private def blockVarianceQuadratic {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) : QuadraticMap ℝ (Fin (J + 1) → ℝ) ℝ :=
  blockSecondMomentQuadratic B n alpha -
    QuadraticMap.linMulLin (blockMeanLinear B n alpha)
      (blockMeanLinear B n alpha)

@[simp] private theorem blockVarianceQuadratic_apply {J : ℕ}
    (B : BlockData J) (n : ℕ) (alpha : ℝ)
    (u : Fin (J + 1) → ℝ) :
    blockVarianceQuadratic B n alpha u = blockEscortVar B n alpha u := by
  simp [blockVarianceQuadratic, blockEscortVar]
  ring

private def blockSecondQuadratic {J : ℕ} (B : BlockData J)
    (jTop : Fin (J + 1)) (n : ℕ) (beta : Param) :
    QuadraticMap ℝ (Fin (J + 1) → ℝ) ℝ :=
  if beta = ⊤ then
    QuadraticMap.proj jTop jTop -
      QuadraticMap.linMulLin (blockMeanLinear B n 1)
        (blockMeanLinear B n 1)
  else if beta = 0 then 0
  else if beta = 1 then
    -blockVarianceQuadratic B n 1 -
      (2 : ℝ) • QuadraticMap.linMulLin (blockMeanLinear B n 1)
        (blockFirstLinear B jTop n 1)
  else
    (-ENNReal.toReal beta) •
        blockVarianceQuadratic B n (ENNReal.toReal beta) +
      singularWeight beta •
        (QuadraticMap.linMulLin (blockMeanLinear B n 1)
            (blockMeanLinear B n 1) -
          QuadraticMap.linMulLin (blockMeanLinear B n (ENNReal.toReal beta))
            (blockMeanLinear B n (ENNReal.toReal beta)))

@[simp] private theorem blockSecondQuadratic_apply {J : ℕ} (B : BlockData J)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop)
    (n : ℕ) (beta : Param) (u : Fin (J + 1) → ℝ) :
    blockSecondQuadratic B jTop n beta u = blockKernelSecond B n u beta := by
  by_cases hbetaTop : beta = (⊤ : Param)
  · subst beta
    simp [blockSecondQuadratic, blockKernelSecond_top_eq B jTop hTop]
    ring
  by_cases hbetaZero : beta = (0 : Param)
  · subst beta
    letI := blockCarrierNonempty B n
    have hz : blockKernelSecond B n u 0 = 0 := by
      exact entropyLineSecond_zero (blockLineData B n u) (linePositiveZero _)
    rw [hz]
    simp [blockSecondQuadratic]
  by_cases hbetaOne : beta = (1 : Param)
  · subst beta
    rw [blockKernelSecond_one]
    simp [blockSecondQuadratic, blockFirstLinear_apply B jTop hTop]
    ring
  have hrealPos : 0 < ENNReal.toReal beta :=
    ENNReal.toReal_pos hbetaZero hbetaTop
  have hrealOne : ENNReal.toReal beta ≠ 1 := by
    intro h
    have hback := finiteParam_paramToReal beta hbetaTop
    rw [show paramToReal beta hbetaTop = ENNReal.toReal beta by rfl,
      h, finiteParam_one] at hback
    exact hbetaOne hback.symm
  have hback := finiteParam_paramToReal beta hbetaTop
  rw [show paramToReal beta hbetaTop = ENNReal.toReal beta by rfl] at hback
  have hk : blockKernelSecond B n u beta =
      -ENNReal.toReal beta * blockEscortVar B n (ENNReal.toReal beta) u +
        singularWeight beta *
          ((blockEscortMean B n 1 u) ^ 2 -
            (blockEscortMean B n (ENNReal.toReal beta) u) ^ 2) := by
    rw [← hback, blockKernelSecond_finite B n u hrealPos hrealOne]
    simp only [finiteParam, ENNReal.toReal_ofReal hrealPos.le]
  rw [hk]
  simp only [blockSecondQuadratic, hbetaTop, if_false, hbetaZero, hbetaOne,
    QuadraticMap.add_apply, QuadraticMap.smul_apply,
    blockVarianceQuadratic_apply, QuadraticMap.sub_apply,
    QuadraticMap.linMulLin_apply, blockMeanLinear_apply, smul_eq_mul]
  ring

private theorem blockKernelIntegrable {J : ℕ} (B : BlockData J)
    (mu : SignedMeasure Param) (n : ℕ) (u : Fin (J + 1) → ℝ)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop) :
    (Integrable (blockKernelFirst B n u) (signedPos mu) ∧
      Integrable (blockKernelFirst B n u) (signedNeg mu)) ∧
    (Integrable (blockKernelSecond B n u) (signedPos mu) ∧
      Integrable (blockKernelSecond B n u) (signedNeg mu)) := by
  letI := blockCarrierNonempty B n
  have H := blockSignedDifferentiation B mu n u jTop hTop
  exact ⟨H.1, H.2.1⟩

private def blockGFirstLinear {J : ℕ} (mu : SignedMeasure Param)
    (B : BlockData J) (n : ℕ) (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop) :
    (Fin (J + 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun u := blockGKernel mu B n u 1
  map_add' u v := by
    rw [(blockGKernelIntegralBridge mu B n (u + v) jTop hTop).1,
      (blockGKernelIntegralBridge mu B n u jTop hTop).1,
      (blockGKernelIntegralBridge mu B n v jTop hTop).1]
    have hu := (blockKernelIntegrable B mu n u jTop hTop).1
    have hv := (blockKernelIntegrable B mu n v jTop hTop).1
    rw [← signedIntegral_add mu hu.1 hu.2 hv.1 hv.2]
    congr 1
    funext beta
    rw [← blockFirstLinear_apply B jTop hTop,
      ← blockFirstLinear_apply B jTop hTop,
      ← blockFirstLinear_apply B jTop hTop]
    exact LinearMap.map_add _ _ _
  map_smul' c u := by
    rw [(blockGKernelIntegralBridge mu B n (c • u) jTop hTop).1,
      (blockGKernelIntegralBridge mu B n u jTop hTop).1]
    rw [show (fun beta => blockKernelFirst B n (c • u) beta) =
        fun beta => c * blockKernelFirst B n u beta by
      funext beta
      rw [← blockFirstLinear_apply B jTop hTop,
        ← blockFirstLinear_apply B jTop hTop]
      exact LinearMap.map_smul_of_tower _ _ _]
    rw [signedIntegral_smul]
    rfl

@[simp] private theorem blockGFirstLinear_apply {J : ℕ}
    (mu : SignedMeasure Param) (B : BlockData J) (n : ℕ)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop)
    (u : Fin (J + 1) → ℝ) :
    blockGFirstLinear mu B n jTop hTop u = blockGKernel mu B n u 1 := rfl

private def blockSecondPolar {J : ℕ} (B : BlockData J)
    (jTop : Fin (J + 1)) (n : ℕ) (u v : Fin (J + 1) → ℝ)
    (beta : Param) : ℝ :=
  QuadraticMap.polar (blockSecondQuadratic B jTop n beta) u v

private theorem blockSecondPolarIntegrable {J : ℕ} (B : BlockData J)
    (mu : SignedMeasure Param) (n : ℕ) (u v : Fin (J + 1) → ℝ)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop) :
    Integrable (blockSecondPolar B jTop n u v) (signedPos mu) ∧
      Integrable (blockSecondPolar B jTop n u v) (signedNeg mu) := by
  have huv := (blockKernelIntegrable B mu n (u + v) jTop hTop).2
  have hu := (blockKernelIntegrable B mu n u jTop hTop).2
  have hv := (blockKernelIntegrable B mu n v jTop hTop).2
  have heq : blockSecondPolar B jTop n u v = fun beta =>
      blockKernelSecond B n (u + v) beta - blockKernelSecond B n u beta -
        blockKernelSecond B n v beta := by
    funext beta
    simp only [blockSecondPolar, QuadraticMap.polar,
      blockSecondQuadratic_apply B jTop hTop]
  rw [heq]
  exact ⟨(huv.1.sub hu.1).sub hv.1, (huv.2.sub hu.2).sub hv.2⟩

private def blockGSecondCompanion {J : ℕ} (mu : SignedMeasure Param)
    (B : BlockData J) (n : ℕ) (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop) :
    (Fin (J + 1) → ℝ) →ₗ[ℝ] (Fin (J + 1) → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v => signedIntegral mu (blockSecondPolar B jTop n u v))
    (fun u u' v => by
      have hu := blockSecondPolarIntegrable B mu n u v jTop hTop
      have hu' := blockSecondPolarIntegrable B mu n u' v jTop hTop
      rw [show blockSecondPolar B jTop n (u + u') v = fun beta =>
          blockSecondPolar B jTop n u v beta +
            blockSecondPolar B jTop n u' v beta by
        funext beta
        exact QuadraticMap.polar_add_left
          (blockSecondQuadratic B jTop n beta) u u' v]
      exact signedIntegral_add mu hu.1 hu.2 hu'.1 hu'.2)
    (fun c u v => by
      rw [show blockSecondPolar B jTop n (c • u) v = fun beta =>
          c * blockSecondPolar B jTop n u v beta by
        funext beta
        simpa only [blockSecondPolar, smul_eq_mul] using QuadraticMap.polar_smul_left
          (blockSecondQuadratic B jTop n beta) c u v]
      exact signedIntegral_smul mu c _)
    (fun u v v' => by
      have hv := blockSecondPolarIntegrable B mu n u v jTop hTop
      have hv' := blockSecondPolarIntegrable B mu n u v' jTop hTop
      rw [show blockSecondPolar B jTop n u (v + v') = fun beta =>
          blockSecondPolar B jTop n u v beta +
            blockSecondPolar B jTop n u v' beta by
        funext beta
        exact QuadraticMap.polar_add_right
          (blockSecondQuadratic B jTop n beta) u v v']
      exact signedIntegral_add mu hv.1 hv.2 hv'.1 hv'.2)
    (fun c u v => by
      rw [show blockSecondPolar B jTop n u (c • v) = fun beta =>
          c * blockSecondPolar B jTop n u v beta by
        funext beta
        simpa only [blockSecondPolar, smul_eq_mul] using QuadraticMap.polar_smul_right
          (blockSecondQuadratic B jTop n beta) c u v]
      exact signedIntegral_smul mu c _)

private def blockGSecondQuadratic {J : ℕ} (mu : SignedMeasure Param)
    (B : BlockData J) (n : ℕ) (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop) :
    QuadraticMap ℝ (Fin (J + 1) → ℝ) ℝ where
  toFun u := blockGKernel mu B n u 2
  toFun_smul c u := by
    rw [(blockGKernelIntegralBridge mu B n (c • u) jTop hTop).2,
      (blockGKernelIntegralBridge mu B n u jTop hTop).2]
    rw [show (fun beta => blockKernelSecond B n (c • u) beta) =
        fun beta => (c * c) * blockKernelSecond B n u beta by
      funext beta
      rw [← blockSecondQuadratic_apply B jTop hTop,
        ← blockSecondQuadratic_apply B jTop hTop]
      simpa only [smul_eq_mul] using
        (blockSecondQuadratic B jTop n beta).map_smul c u]
    rw [signedIntegral_smul]
    rfl
  exists_companion' := ⟨blockGSecondCompanion mu B n jTop hTop, by
    intro u v
    rw [(blockGKernelIntegralBridge mu B n (u + v) jTop hTop).2,
      (blockGKernelIntegralBridge mu B n u jTop hTop).2,
      (blockGKernelIntegralBridge mu B n v jTop hTop).2]
    have hu := (blockKernelIntegrable B mu n u jTop hTop).2
    have hv := (blockKernelIntegrable B mu n v jTop hTop).2
    have hp := blockSecondPolarIntegrable B mu n u v jTop hTop
    rw [show (fun beta => blockKernelSecond B n (u + v) beta) = fun beta =>
        blockKernelSecond B n u beta + blockKernelSecond B n v beta +
          blockSecondPolar B jTop n u v beta by
      funext beta
      rw [← blockSecondQuadratic_apply B jTop hTop,
        ← blockSecondQuadratic_apply B jTop hTop,
        ← blockSecondQuadratic_apply B jTop hTop]
      exact QuadraticMap.map_add _ _ _]
    calc
      signedIntegral mu (fun beta =>
          blockKernelSecond B n u beta + blockKernelSecond B n v beta +
            blockSecondPolar B jTop n u v beta) =
          signedIntegral mu (fun beta =>
            blockKernelSecond B n u beta + blockKernelSecond B n v beta) +
            signedIntegral mu (blockSecondPolar B jTop n u v) :=
        signedIntegral_add mu (hu.1.add hv.1) (hu.2.add hv.2) hp.1 hp.2
      _ = signedIntegral mu (blockKernelSecond B n u) +
            signedIntegral mu (blockKernelSecond B n v) +
              signedIntegral mu (blockSecondPolar B jTop n u v) := by
        rw [signedIntegral_add mu hu.1 hu.2 hv.1 hv.2]
      _ = signedIntegral mu (blockKernelSecond B n u) +
            signedIntegral mu (blockKernelSecond B n v) +
              blockGSecondCompanion mu B n jTop hTop u v := rfl⟩

@[simp] private theorem blockGSecondQuadratic_apply {J : ℕ}
    (mu : SignedMeasure Param) (B : BlockData J) (n : ℕ)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop)
    (u : Fin (J + 1) → ℝ) :
    blockGSecondQuadratic mu B n jTop hTop u = blockGKernel mu B n u 2 := rfl

set_option maxHeartbeats 800000 in
-- Converting the finite-dimensional quadratic companion to a continuous bilinear map is intensive.
/-- The first norm-free block kernel is linear in the velocity and the first
two norm-free block kernels are continuous in that finite-dimensional
velocity. -/
theorem blockKernelRegularity {J : ℕ} (mu : SignedMeasure Param)
    (B : BlockData J) (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop)
    (n : ℕ) :
    (∀ u v : Fin (J + 1) → ℝ,
      blockGKernel mu B n (u + v) 1 =
        blockGKernel mu B n u 1 + blockGKernel mu B n v 1) ∧
    (∀ (c : ℝ) (u : Fin (J + 1) → ℝ),
      blockGKernel mu B n (c • u) 1 = c * blockGKernel mu B n u 1) ∧
    Continuous (fun u : Fin (J + 1) → ℝ => blockGKernel mu B n u 1) ∧
    Continuous (fun u : Fin (J + 1) → ℝ => blockGKernel mu B n u 2) := by
  let A := blockGFirstLinear mu B n jTop hTop
  let Q := blockGSecondQuadratic mu B n jTop hTop
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v
    exact A.map_add u v
  · intro c u
    change A (c • u) = c * A u
    simpa only [smul_eq_mul] using A.map_smul c u
  · exact A.continuous_of_finiteDimensional
  · let P := QuadraticMap.associatedHom ℝ Q
    let Pc := P.toContinuousBilinearMap
    have hdiag : Continuous (fun u : Fin (J + 1) → ℝ => Pc u u) :=
      Pc.continuous₂.comp₂ continuous_id continuous_id
    have hdiag' : Continuous (fun u : Fin (J + 1) → ℝ => P u u) := by
      simpa only [Pc, LinearMap.toContinuousBilinearMap_apply] using hdiag
    change Continuous Q
    convert hdiag' using 1
    funext u
    exact (QuadraticMap.associated_eq_self_apply ℝ Q u).symm

/-- Exact splitting of logarithmic block kernels together with the two
compact-uniform logarithmic-mass limits. -/
theorem blockLogMassLimit {J : ℕ} (B : BlockData J)
    (mu : SignedMeasure Param) (k : Fin (J + 1))
    (hk : ∀ j : Fin (J + 1), j ≠ k →
      blockExponent B j 1 < blockExponent B k 1)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop) :
    (∀ (n : ℕ) (u : Fin (J + 1) → ℝ) (q : ℕ), q ≤ 2 →
      blockLogKernel mu B n u q =
        blockLogMassKernel B n u q + blockGKernel mu B n u q) ∧
    (∀ K : Set (Fin (J + 1) → ℝ), K.Nonempty → IsCompact K →
      CompactUniformConverges K
          (fun n u => blockLogMassKernel B n u 1) (fun u => u k) ∧
        CompactUniformConverges K
          (fun n u => blockLogMassKernel B n u 2) (fun u => -(u k) ^ 2)) := by
  constructor
  · intro n u q hq
    interval_cases q
    · rfl
    · letI := blockCarrierNonempty B n
      have H := blockSignedDifferentiation B mu n u jTop hTop
      rw [(blockGKernelIntegralBridge mu B n u jTop hTop).1]
      change iteratedDeriv (signedLogPhiLine mu (blockLineData B n u)) 1 0 =
        iteratedDeriv (fun lambda => Real.log (blockMass B n u lambda)) 1 0 +
          signedIntegral mu (fun beta =>
            entropyLineFirst (blockLineData B n u) beta 0)
      have hmass : (fun lambda => Real.log (blockMass B n u lambda)) =
          fun lambda => Real.log (lineMass (blockLineData B n u) lambda) := by
        funext lambda
        rw [blockMass_eq_lineMass]
      rw [hmass]
      have hs := H.2.2.2.2.1
      change deriv (signedLogPhiLine mu (blockLineData B n u)) 0 =
        deriv (fun lambda => Real.log (lineMass (blockLineData B n u) lambda)) 0 +
          signedIntegral mu (fun beta =>
            entropyLineFirst (blockLineData B n u) beta 0) at hs
      change deriv (signedLogPhiLine mu (blockLineData B n u)) 0 =
        deriv (fun lambda => Real.log (lineMass (blockLineData B n u) lambda)) 0 +
          signedIntegral mu (fun beta =>
            entropyLineFirst (blockLineData B n u) beta 0)
      exact hs
    · letI := blockCarrierNonempty B n
      have H := blockSignedDifferentiation B mu n u jTop hTop
      rw [(blockGKernelIntegralBridge mu B n u jTop hTop).2]
      change iteratedDeriv (signedLogPhiLine mu (blockLineData B n u)) 2 0 =
        iteratedDeriv (fun lambda => Real.log (blockMass B n u lambda)) 2 0 +
          signedIntegral mu (fun beta =>
            entropyLineSecond (blockLineData B n u) beta 0)
      have hmass : (fun lambda => Real.log (blockMass B n u lambda)) =
          fun lambda => Real.log (lineMass (blockLineData B n u) lambda) := by
        funext lambda
        rw [blockMass_eq_lineMass]
      rw [hmass]
      have hs := H.2.2.2.2.2.1
      change deriv (deriv (signedLogPhiLine mu (blockLineData B n u))) 0 =
        deriv (deriv (fun lambda =>
          Real.log (lineMass (blockLineData B n u) lambda))) 0 +
          signedIntegral mu (fun beta =>
            entropyLineSecond (blockLineData B n u) beta 0) at hs
      change deriv (deriv (signedLogPhiLine mu (blockLineData B n u))) 0 =
        deriv (deriv (fun lambda =>
          Real.log (lineMass (blockLineData B n u) lambda))) 0 +
          signedIntegral mu (fun beta =>
            entropyLineSecond (blockLineData B n u) beta 0)
      exact hs
  · intro K hK0 hK
    exact blockLogMassKernelLimits B k hk K hK0 hK

private theorem compactUniformConverges_signedIntegral
    {E U : Type*} [MeasurableSpace E]
    (mu : SignedMeasure E) (K : Set U)
    (fN : ℕ → E → U → ℝ) (f : E → U → ℝ)
    (FN : ℕ → U → ℝ) (F : U → ℝ)
    (hFN : ∀ n u, signedIntegral mu (fun e => fN n e u) = FN n u)
    (hF : ∀ u, signedIntegral mu (fun e => f e u) = F u)
    (H : Tendsto (fun n => uniformIntegralErrorSigned mu
      (fun m e (u : {x : U // x ∈ K}) => fN m e u.1)
      (fun e (u : {x : U // x ∈ K}) => f e u.1) n)
      atTop (nhds 0)) :
    CompactUniformConverges K FN F := by
  have herr : ∀ n,
      uniformIntegralErrorSigned mu
        (fun m e (u : {x : U // x ∈ K}) => fN m e u.1)
        (fun e (u : {x : U // x ∈ K}) => f e u.1) n =
          compactUniformError K FN F n := by
    intro n
    rw [subtypeUniformErrorBridge mu K fN f n]
    congr 1
    · funext m u
      exact hFN m u
    · funext u
      exact hF u
  unfold CompactUniformConverges
  simpa only [herr] using H

/-- Exact two-block compact-uniform localization interface. -/
theorem twoBlockLocalization
    (mu : SignedMeasure Param) (r R : ℝ)
    (hr : 0 < r) (hr1 : r ≠ 1) (hR : r < R)
    (K : Set (Fin 2 → ℝ)) (hK0 : K.Nonempty) (hK : IsCompact K)
    (hmuR : signedTV mu ({finiteParam r} : Set Param) = 0) :
    let B := twoBlockData r R hr hR
    (1 < r →
      CompactUniformConverges K
        (fun n u => blockLogKernel mu B n u 1)
        (fun u => twoUpperLogFirst mu r u) ∧
      CompactUniformConverges K
        (fun n u => blockLogKernel mu B n u 2)
        (fun u => twoUpperLogSecond mu r u) ∧
      CompactUniformConverges K
        (fun n u => blockGKernel mu B n u 1)
        (fun u => twoUpperGFirst mu r u) ∧
      CompactUniformConverges K
        (fun n u => blockGKernel mu B n u 2)
        (fun u => twoUpperGSecond mu r u)) ∧
    (r < 1 →
      CompactUniformConverges K
        (fun n u => blockLogKernel mu B n u 1)
        (fun u => twoLowerLogFirst mu r u) ∧
      CompactUniformConverges K
        (fun n u => blockLogKernel mu B n u 2)
        (fun u => twoLowerLogSecond mu r u) ∧
      CompactUniformConverges K
        (fun n u => blockGKernel mu B n u 1)
        (fun u => twoLowerGFirst mu r u) ∧
      CompactUniformConverges K
        (fun n u => blockGKernel mu B n u 2)
        (fun u => twoLowerGSecond mu r u)) := by
  dsimp only
  let B := twoBlockData r R hr hR
  let P := twoBlockDominancePackage r R hr hR
  have H := blockLimitPassage B mu ({r} : Finset ℝ)
    (twoDominanceMap r) 1
    (by simpa [eq_comm] using hr1)
    (by
      intro s hs
      simp only [Finset.mem_singleton] at hs
      subst s
      exact hmuR)
    P.1 P.2.1 P.2.2 (twoBlockTopUnique r R hr hR) K hK hK0
  dsimp only at H
  constructor
  · intro h1r
    have HG1 : CompactUniformConverges K
        (fun n u => blockGKernel mu B n u 1)
        (fun u => twoUpperGFirst mu r u) :=
      compactUniformConverges_signedIntegral mu K
        (fun n beta u => blockKernelFirst B n u beta)
        (fun beta u => blockLimitFirst (twoDominanceMap r) u beta)
        (fun n u => blockGKernel mu B n u 1)
        (fun u => twoUpperGFirst mu r u)
        (fun n u => (blockGKernelIntegralBridge mu B n u 1
          (twoBlockTopUnique r R hr hR)).1.symm)
        (fun u => ((twoBlockLimitIntegralEval mu r hr u hmuR).1 h1r).1)
        H.2.2.2.2.1
    have HG2 : CompactUniformConverges K
        (fun n u => blockGKernel mu B n u 2)
        (fun u => twoUpperGSecond mu r u) :=
      compactUniformConverges_signedIntegral mu K
        (fun n beta u => blockKernelSecond B n u beta)
        (fun beta u => blockLimitSecond (twoDominanceMap r) u beta)
        (fun n u => blockGKernel mu B n u 2)
        (fun u => twoUpperGSecond mu r u)
        (fun n u => (blockGKernelIntegralBridge mu B n u 1
          (twoBlockTopUnique r R hr hR)).2.symm)
        (fun u => ((twoBlockLimitIntegralEval mu r hr u hmuR).1 h1r).2)
        H.2.2.2.2.2
    have hMassSplit := blockLogMassLimit B mu 0
      ((twoOrderOneDominancePackage r R hr hR).1 h1r) 1
      (twoBlockTopUnique r R hr hR)
    have HM := hMassSplit.2 K hK0 hK
    have Hsum1 := compactUniformConverges_add K hK0 hK
      (fun n u => blockLogMassKernel B n u 1)
      (fun n u => blockGKernel mu B n u 1)
      (fun u => u 0) (fun u => twoUpperGFirst mu r u)
      (fun n => (blockLogMassKernelContinuous B n 1 (by norm_num)).continuousOn)
      (fun n => ((blockKernelRegularity mu B 1
        (twoBlockTopUnique r R hr hR) n).2.2.1).continuousOn)
      (continuous_apply 0).continuousOn
      (continuous_twoUpperGFirst mu r).continuousOn HM.1 HG1
    have Hsum2 := compactUniformConverges_add K hK0 hK
      (fun n u => blockLogMassKernel B n u 2)
      (fun n u => blockGKernel mu B n u 2)
      (fun u => -(u 0) ^ 2) (fun u => twoUpperGSecond mu r u)
      (fun n => (blockLogMassKernelContinuous B n 2 (by norm_num)).continuousOn)
      (fun n => ((blockKernelRegularity mu B 1
        (twoBlockTopUnique r R hr hR) n).2.2.2).continuousOn)
      (((continuous_apply 0).pow 2).neg).continuousOn
      (continuous_twoUpperGSecond mu r).continuousOn HM.2 HG2
    have hsplit1 : ∀ n u, blockLogKernel mu B n u 1 =
        blockLogMassKernel B n u 1 + blockGKernel mu B n u 1 :=
      fun n u => hMassSplit.1 n u 1 (by norm_num)
    have hsplit2 : ∀ n u, blockLogKernel mu B n u 2 =
        blockLogMassKernel B n u 2 + blockGKernel mu B n u 2 :=
      fun n u => hMassSplit.1 n u 2 (by norm_num)
    have HL1 : CompactUniformConverges K
        (fun n u => blockLogKernel mu B n u 1)
        (fun u => twoUpperLogFirst mu r u) := by
      simpa only [hsplit1, twoUpperLogFirst_eq_mass_add_g] using Hsum1
    have HL2 : CompactUniformConverges K
        (fun n u => blockLogKernel mu B n u 2)
        (fun u => twoUpperLogSecond mu r u) := by
      simpa only [hsplit2, twoUpperLogSecond_eq_mass_add_g] using Hsum2
    exact ⟨HL1, HL2, HG1, HG2⟩
  · intro hr1'
    have HG1 : CompactUniformConverges K
        (fun n u => blockGKernel mu B n u 1)
        (fun u => twoLowerGFirst mu r u) :=
      compactUniformConverges_signedIntegral mu K
        (fun n beta u => blockKernelFirst B n u beta)
        (fun beta u => blockLimitFirst (twoDominanceMap r) u beta)
        (fun n u => blockGKernel mu B n u 1)
        (fun u => twoLowerGFirst mu r u)
        (fun n u => (blockGKernelIntegralBridge mu B n u 1
          (twoBlockTopUnique r R hr hR)).1.symm)
        (fun u => ((twoBlockLimitIntegralEval mu r hr u hmuR).2 hr1').1)
        H.2.2.2.2.1
    have HG2 : CompactUniformConverges K
        (fun n u => blockGKernel mu B n u 2)
        (fun u => twoLowerGSecond mu r u) :=
      compactUniformConverges_signedIntegral mu K
        (fun n beta u => blockKernelSecond B n u beta)
        (fun beta u => blockLimitSecond (twoDominanceMap r) u beta)
        (fun n u => blockGKernel mu B n u 2)
        (fun u => twoLowerGSecond mu r u)
        (fun n u => (blockGKernelIntegralBridge mu B n u 1
          (twoBlockTopUnique r R hr hR)).2.symm)
        (fun u => ((twoBlockLimitIntegralEval mu r hr u hmuR).2 hr1').2)
        H.2.2.2.2.2
    have hMassSplit := blockLogMassLimit B mu 1
      ((twoOrderOneDominancePackage r R hr hR).2 hr1') 1
      (twoBlockTopUnique r R hr hR)
    have HM := hMassSplit.2 K hK0 hK
    have Hsum1 := compactUniformConverges_add K hK0 hK
      (fun n u => blockLogMassKernel B n u 1)
      (fun n u => blockGKernel mu B n u 1)
      (fun u => u 1) (fun u => twoLowerGFirst mu r u)
      (fun n => (blockLogMassKernelContinuous B n 1 (by norm_num)).continuousOn)
      (fun n => ((blockKernelRegularity mu B 1
        (twoBlockTopUnique r R hr hR) n).2.2.1).continuousOn)
      (continuous_apply 1).continuousOn
      (continuous_twoLowerGFirst mu r).continuousOn HM.1 HG1
    have Hsum2 := compactUniformConverges_add K hK0 hK
      (fun n u => blockLogMassKernel B n u 2)
      (fun n u => blockGKernel mu B n u 2)
      (fun u => -(u 1) ^ 2) (fun u => twoLowerGSecond mu r u)
      (fun n => (blockLogMassKernelContinuous B n 2 (by norm_num)).continuousOn)
      (fun n => ((blockKernelRegularity mu B 1
        (twoBlockTopUnique r R hr hR) n).2.2.2).continuousOn)
      (((continuous_apply 1).pow 2).neg).continuousOn
      (continuous_twoLowerGSecond mu r).continuousOn HM.2 HG2
    have hsplit1 : ∀ n u, blockLogKernel mu B n u 1 =
        blockLogMassKernel B n u 1 + blockGKernel mu B n u 1 :=
      fun n u => hMassSplit.1 n u 1 (by norm_num)
    have hsplit2 : ∀ n u, blockLogKernel mu B n u 2 =
        blockLogMassKernel B n u 2 + blockGKernel mu B n u 2 :=
      fun n u => hMassSplit.1 n u 2 (by norm_num)
    have HL1 : CompactUniformConverges K
        (fun n u => blockLogKernel mu B n u 1)
        (fun u => twoLowerLogFirst mu r u) := by
      simpa only [hsplit1, twoLowerLogFirst_eq_mass_add_g] using Hsum1
    have HL2 : CompactUniformConverges K
        (fun n u => blockLogKernel mu B n u 2)
        (fun u => twoLowerLogSecond mu r u) := by
      simpa only [hsplit2, twoLowerLogSecond_eq_mass_add_g] using Hsum2
    exact ⟨HL1, HL2, HG1, HG2⟩

/-- Exact three-block compact-uniform localization interface. -/
theorem threeBlockLocalization
    (mu : SignedMeasure Param) (a b R : ℝ)
    (ha : 0 < a) (hab : a < b) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hR : a + b < R)
    (K : Set (Fin 3 → ℝ)) (hK0 : K.Nonempty) (hK : IsCompact K)
    (hmu : signedTV mu ({finiteParam a} : Set Param) = 0 ∧
      signedTV mu ({finiteParam b} : Set Param) = 0) :
    let B := threeBlockData a b R ha hab hR
    CompactUniformConverges K
        (fun n u => blockLogKernel mu B n u 1)
        (fun u => threeLogFirst mu a b u) ∧
      CompactUniformConverges K
        (fun n u => blockLogKernel mu B n u 2)
        (fun u => threeLogSecond mu a b u) ∧
      CompactUniformConverges K
        (fun n u => blockGKernel mu B n u 1)
        (fun u => threeGFirst mu a b u) ∧
      CompactUniformConverges K
        (fun n u => blockGKernel mu B n u 2)
        (fun u => threeGSecond mu a b u) := by
  rcases hmu with ⟨hmuA, hmuB⟩
  dsimp only
  let B := threeBlockData a b R ha hab hR
  let P := threeBlockDominancePackage a b R ha hab hR
  have H := blockLimitPassage B mu ({a, b} : Finset ℝ)
    (threeDominanceMap a b) 2
    (by simpa [eq_comm] using And.intro ha1 hb1)
    (by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact hmuA
      · exact hmuB)
    P.1 P.2.1 P.2.2 (threeBlockTopUnique a b R ha hab hR) K hK hK0
  dsimp only at H
  have HG1 : CompactUniformConverges K
      (fun n u => blockGKernel mu B n u 1)
      (fun u => threeGFirst mu a b u) :=
    compactUniformConverges_signedIntegral mu K
      (fun n beta u => blockKernelFirst B n u beta)
      (fun beta u => blockLimitFirst (threeDominanceMap a b) u beta)
      (fun n u => blockGKernel mu B n u 1)
      (fun u => threeGFirst mu a b u)
      (fun n u => (blockGKernelIntegralBridge mu B n u 2
        (threeBlockTopUnique a b R ha hab hR)).1.symm)
      (fun u => (threeBlockLimitIntegralEval mu a b ha hab ha1 hb1 u
        hmuA hmuB).1)
      H.2.2.2.2.1
  have HG2 : CompactUniformConverges K
      (fun n u => blockGKernel mu B n u 2)
      (fun u => threeGSecond mu a b u) :=
    compactUniformConverges_signedIntegral mu K
      (fun n beta u => blockKernelSecond B n u beta)
      (fun beta u => blockLimitSecond (threeDominanceMap a b) u beta)
      (fun n u => blockGKernel mu B n u 2)
      (fun u => threeGSecond mu a b u)
      (fun n u => (blockGKernelIntegralBridge mu B n u 2
        (threeBlockTopUnique a b R ha hab hR)).2.symm)
      (fun u => (threeBlockLimitIntegralEval mu a b ha hab ha1 hb1 u
        hmuA hmuB).2)
      H.2.2.2.2.2
  have hMassSplit := blockLogMassLimit B mu (threeNormBlock a b)
    (threeOrderOneDominant a b R ha hab hR ha1 hb1) 2
    (threeBlockTopUnique a b R ha hab hR)
  have HM := hMassSplit.2 K hK0 hK
  have Hsum1 := compactUniformConverges_add K hK0 hK
    (fun n u => blockLogMassKernel B n u 1)
    (fun n u => blockGKernel mu B n u 1)
    (fun u => u (threeNormBlock a b)) (fun u => threeGFirst mu a b u)
    (fun n => (blockLogMassKernelContinuous B n 1 (by norm_num)).continuousOn)
    (fun n => ((blockKernelRegularity mu B 2
      (threeBlockTopUnique a b R ha hab hR) n).2.2.1).continuousOn)
    (continuous_apply (threeNormBlock a b)).continuousOn
    (continuous_threeGFirst mu a b).continuousOn HM.1 HG1
  have Hsum2 := compactUniformConverges_add K hK0 hK
    (fun n u => blockLogMassKernel B n u 2)
    (fun n u => blockGKernel mu B n u 2)
    (fun u => -(u (threeNormBlock a b)) ^ 2)
    (fun u => threeGSecond mu a b u)
    (fun n => (blockLogMassKernelContinuous B n 2 (by norm_num)).continuousOn)
    (fun n => ((blockKernelRegularity mu B 2
      (threeBlockTopUnique a b R ha hab hR) n).2.2.2).continuousOn)
    (((continuous_apply (threeNormBlock a b)).pow 2).neg).continuousOn
    (continuous_threeGSecond mu a b).continuousOn HM.2 HG2
  have hsplit1 : ∀ n u, blockLogKernel mu B n u 1 =
      blockLogMassKernel B n u 1 + blockGKernel mu B n u 1 :=
    fun n u => hMassSplit.1 n u 1 (by norm_num)
  have hsplit2 : ∀ n u, blockLogKernel mu B n u 2 =
      blockLogMassKernel B n u 2 + blockGKernel mu B n u 2 :=
    fun n u => hMassSplit.1 n u 2 (by norm_num)
  have HL1 : CompactUniformConverges K
      (fun n u => blockLogKernel mu B n u 1)
      (fun u => threeLogFirst mu a b u) := by
    simpa only [hsplit1, threeLogFirst_eq_mass_add_g] using Hsum1
  have HL2 : CompactUniformConverges K
      (fun n u => blockLogKernel mu B n u 2)
      (fun u => threeLogSecond mu a b u) := by
    simpa only [hsplit2, threeLogSecond_eq_mass_add_g] using Hsum2
  exact ⟨HL1, HL2, HG1, HG2⟩

/-- Literal combined two- and three-block localization proposition. -/
theorem blockLocalization
    (mu : SignedMeasure Param)
    (r R : ℝ) (hr : 0 < r) (hr1 : r ≠ 1) (hR : r < R)
    (K2 : Set (Fin 2 → ℝ)) (hK20 : K2.Nonempty) (hK2 : IsCompact K2)
    (a b R3 : ℝ) (ha : 0 < a) (hab : a < b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hR3 : a + b < R3)
    (K3 : Set (Fin 3 → ℝ)) (hK30 : K3.Nonempty) (hK3 : IsCompact K3)
    (hmuR : signedTV mu ({finiteParam r} : Set Param) = 0)
    (hmuA : signedTV mu ({finiteParam a} : Set Param) = 0)
    (hmuB : signedTV mu ({finiteParam b} : Set Param) = 0) :
    let B2 := twoBlockData r R hr hR
    let B3 := threeBlockData a b R3 ha hab hR3
    (1 < r →
      Tendsto (fun n => compactUniformError K2
        (fun m u => blockLogKernel mu B2 m u 1)
        (fun u => twoUpperLogFirst mu r u) n) atTop (nhds 0) ∧
      Tendsto (fun n => compactUniformError K2
        (fun m u => blockLogKernel mu B2 m u 2)
        (fun u => twoUpperLogSecond mu r u) n) atTop (nhds 0) ∧
      Tendsto (fun n => compactUniformError K2
        (fun m u => blockGKernel mu B2 m u 1)
        (fun u => twoUpperGFirst mu r u) n) atTop (nhds 0) ∧
      Tendsto (fun n => compactUniformError K2
        (fun m u => blockGKernel mu B2 m u 2)
        (fun u => twoUpperGSecond mu r u) n) atTop (nhds 0)) ∧
    (r < 1 →
      Tendsto (fun n => compactUniformError K2
        (fun m u => blockLogKernel mu B2 m u 1)
        (fun u => twoLowerLogFirst mu r u) n) atTop (nhds 0) ∧
      Tendsto (fun n => compactUniformError K2
        (fun m u => blockLogKernel mu B2 m u 2)
        (fun u => twoLowerLogSecond mu r u) n) atTop (nhds 0) ∧
      Tendsto (fun n => compactUniformError K2
        (fun m u => blockGKernel mu B2 m u 1)
        (fun u => twoLowerGFirst mu r u) n) atTop (nhds 0) ∧
      Tendsto (fun n => compactUniformError K2
        (fun m u => blockGKernel mu B2 m u 2)
        (fun u => twoLowerGSecond mu r u) n) atTop (nhds 0)) ∧
    Tendsto (fun n => compactUniformError K3
      (fun m u => blockLogKernel mu B3 m u 1)
      (fun u => threeLogFirst mu a b u) n) atTop (nhds 0) ∧
    Tendsto (fun n => compactUniformError K3
      (fun m u => blockLogKernel mu B3 m u 2)
      (fun u => threeLogSecond mu a b u) n) atTop (nhds 0) ∧
    Tendsto (fun n => compactUniformError K3
      (fun m u => blockGKernel mu B3 m u 1)
      (fun u => threeGFirst mu a b u) n) atTop (nhds 0) ∧
    Tendsto (fun n => compactUniformError K3
      (fun m u => blockGKernel mu B3 m u 2)
      (fun u => threeGSecond mu a b u) n) atTop (nhds 0) := by
  dsimp only
  have H2 := twoBlockLocalization mu r R hr hr1 hR K2 hK20 hK2 hmuR
  have H3 := threeBlockLocalization mu a b R3 ha hab ha1 hb1 hR3
    K3 hK30 hK3 ⟨hmuA, hmuB⟩
  dsimp only at H2 H3
  exact ⟨H2.1, H2.2, H3.1, H3.2.1, H3.2.2.1, H3.2.2.2⟩

end ConditionalEntropy
