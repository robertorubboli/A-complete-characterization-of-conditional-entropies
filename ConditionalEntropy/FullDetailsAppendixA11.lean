import ConditionalEntropy.EndpointParameterContinuity
import ConditionalEntropy.SignedLineCalculus

/-!
# Appendix A.11: fixed-dimensional differentiation under the parameter integral

This module gives the paper-facing form of Proposition A.11.  The compactified
parameter space makes the first two entropy-line derivatives uniformly bounded
on a closed positive line interval.  Since both Jordan components of a signed
measure are finite, those constant bounds are integrable and the two derivative
interchanges follow from the signed dominated-differentiation theorem.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology ContDiff

namespace ConditionalEntropy

universe u

private theorem fullDetailsA11_hasDerivAt_entropyLine
    {I : Type u} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) {U : Set ℝ} (hU : IsOpen U)
    (hpos : ∀ lambda ∈ U, LinePositive L lambda)
    {istar : I} (hfixed : FixedMaxCoordinate L U istar)
    (beta : Param) {lambda : ℝ} (hlambda : lambda ∈ U) :
    HasDerivAt (entropyLine L beta)
        (entropyLineFirst L beta lambda) lambda ∧
      HasDerivAt (entropyLineFirst L beta)
        (entropyLineSecond L beta lambda) lambda := by
  by_cases htop : beta = ⊤
  · subst beta
    constructor
    · convert hasDerivAt_entropyLine_top_on L hU hfixed hlambda using 1
      exact entropyLineFirst_top_on L hU hfixed hlambda
    · convert hasDerivAt_entropyLineFirst_top_on L hU hfixed hlambda using 1
      exact entropyLineSecond_top_on L hU hfixed hlambda
  · let alpha : ℝ := ENNReal.toReal beta
    have hback : finiteParam alpha = beta := by
      simpa only [alpha, paramToReal] using finiteParam_paramToReal beta htop
    have halpha0 : 0 ≤ alpha := ENNReal.toReal_nonneg
    by_cases hzero : alpha = 0
    · rw [← hback, hzero, finiteParam_zero]
      constructor
      · convert hasDerivAt_entropyLine_zero L (hpos lambda hlambda) using 1
        exact entropyLineFirst_zero L (hpos lambda hlambda)
      · convert hasDerivAt_entropyLineFirst_zero L (hpos lambda hlambda) using 1
        exact entropyLineSecond_zero L (hpos lambda hlambda)
    · by_cases hone : alpha = 1
      · rw [← hback, hone, finiteParam_one]
        constructor
        · convert hasDerivAt_entropyLine_one L (hpos lambda hlambda) using 1
          exact entropyLineFirst_one L (hpos lambda hlambda)
        · convert hasDerivAt_entropyLineFirst_one L (hpos lambda hlambda) using 1
          exact entropyLineSecond_one L (hpos lambda hlambda)
      · rw [← hback]
        have halpha : 0 < alpha := lt_of_le_of_ne halpha0 (Ne.symm hzero)
        constructor
        · convert hasDerivAt_entropyLine_finite_on L hU hpos
            halpha hone hlambda using 1
          exact entropyLineFirst_finite_on L hU hpos halpha hone hlambda
        · convert hasDerivAt_entropyLineFirst_finite_on L hU hpos
            halpha hone hlambda using 1
          exact entropyLineSecond_finite_on L hU hpos halpha hone hlambda

private theorem fullDetailsA11_continuous_param_slice
    {lambda0 : ℝ} {f : Param × ℝ → ℝ}
    (hf : ContinuousOn f (Set.univ ×ˢ Icc (-lambda0) lambda0))
    {lambda : ℝ} (hlambda : lambda ∈ Icc (-lambda0) lambda0) :
    Continuous (fun beta : Param => f (beta, lambda)) := by
  exact hf.comp_continuous (continuous_id.prodMk continuous_const)
    (fun beta => ⟨Set.mem_univ beta, hlambda⟩)

private theorem fullDetailsA11_continuous_line_slice
    {lambda0 : ℝ} {f : Param × ℝ → ℝ}
    (hf : ContinuousOn f (Set.univ ×ˢ Icc (-lambda0) lambda0))
    (beta : Param) :
    ContinuousOn (fun lambda : ℝ => f (beta, lambda))
      (Icc (-lambda0) lambda0) := by
  exact hf.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun lambda hlambda => ⟨Set.mem_univ beta, hlambda⟩)

private theorem fullDetailsA11_continuousOn_signedIntegral
    (mu : SignedMeasure Param) {lambda0 : ℝ} {f : Param × ℝ → ℝ}
    (hf : ContinuousOn f (Set.univ ×ˢ Icc (-lambda0) lambda0))
    (C : ℝ)
    (hC : ∀ beta : Param, ∀ lambda ∈ Icc (-lambda0) lambda0,
      |f (beta, lambda)| ≤ C) :
    ContinuousOn (fun lambda => signedIntegral mu (fun beta => f (beta, lambda)))
      (Ioo (-lambda0) lambda0) := by
  have hsub : Ioo (-lambda0) lambda0 ⊆ Icc (-lambda0) lambda0 := by
    intro lambda hlambda
    exact ⟨hlambda.1.le, hlambda.2.le⟩
  have hposIntegral : ContinuousOn
      (fun lambda => ∫ beta, f (beta, lambda) ∂signedPos mu)
      (Ioo (-lambda0) lambda0) := by
    apply continuousOn_of_dominated
    · intro lambda hlambda
      exact (fullDetailsA11_continuous_param_slice hf
        (hsub hlambda)).aestronglyMeasurable
    · intro lambda hlambda
      exact ae_of_all (signedPos mu) fun beta => by
        simpa only [Real.norm_eq_abs] using hC beta lambda (hsub hlambda)
    · exact integrable_const C
    · exact ae_of_all (signedPos mu) fun beta =>
        (fullDetailsA11_continuous_line_slice hf beta).mono hsub
  have hnegIntegral : ContinuousOn
      (fun lambda => ∫ beta, f (beta, lambda) ∂signedNeg mu)
      (Ioo (-lambda0) lambda0) := by
    apply continuousOn_of_dominated
    · intro lambda hlambda
      exact (fullDetailsA11_continuous_param_slice hf
        (hsub hlambda)).aestronglyMeasurable
    · intro lambda hlambda
      exact ae_of_all (signedNeg mu) fun beta => by
        simpa only [Real.norm_eq_abs] using hC beta lambda (hsub hlambda)
    · exact integrable_const C
    · exact ae_of_all (signedNeg mu) fun beta =>
        (fullDetailsA11_continuous_line_slice hf beta).mono hsub
  unfold signedIntegral
  exact hposIntegral.sub hnegIntegral

private theorem fullDetailsA11_contDiffOn_two
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

/-- Appendix A.11 (Proposition `prop:app-fixed-d-interchange`).

For a strictly positive affine line with a stable maximal coordinate on the
closed interval, integrating endpoint-aware Rényi entropy against an arbitrary
finite signed parameter measure gives a twice continuously differentiable
function on the interior.  Its first and second derivatives are obtained by
integrating the corresponding entropy-line derivatives.  No parameter moment
or finiteness hypothesis beyond finiteness of the signed measure is assumed. -/
theorem fullDetailsAppendixA_11
    {I : Type u} [Fintype I] [Nonempty I]
    (mu : SignedMeasure Param) (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda)
    {istar : I}
    (hfixed : FixedMaxCoordinate L (Icc (-lambda0) lambda0) istar) :
    (ContDiffOn ℝ 2 (integratedEntropyLine mu L)
      (Ioo (-lambda0) lambda0)) ∧
    (∀ lambda ∈ Ioo (-lambda0) lambda0,
      HasDerivAt (integratedEntropyLine mu L)
          (signedIntegral mu
            (fun beta => entropyLineFirst L beta lambda)) lambda ∧
      HasDerivAt
          (fun s => signedIntegral mu
            (fun beta => entropyLineFirst L beta s))
          (signedIntegral mu
            (fun beta => entropyLineSecond L beta lambda)) lambda ∧
      iteratedDeriv (integratedEntropyLine mu L) 1 lambda =
          signedIntegral mu
            (fun beta => entropyLineFirst L beta lambda) ∧
      iteratedDeriv (integratedEntropyLine mu L) 2 lambda =
          signedIntegral mu
            (fun beta => entropyLineSecond L beta lambda)) := by
  have hbundle :=
    continuousOn_entropyLine_full_bundle L hlambda0 hpos hfixed
  let S : Set (Param × ℝ) := Set.univ ×ˢ Icc (-lambda0) lambda0
  have hScompact : IsCompact S := isCompact_univ.prod isCompact_Icc
  obtain ⟨C0, hC0⟩ := hScompact.exists_bound_of_continuousOn hbundle.1
  obtain ⟨C1, hC1⟩ := hScompact.exists_bound_of_continuousOn hbundle.2.1
  obtain ⟨C2, hC2⟩ := hScompact.exists_bound_of_continuousOn hbundle.2.2
  let f0 : ℝ → ℝ := integratedEntropyLine mu L
  let f1 : ℝ → ℝ := fun lambda =>
    signedIntegral mu (fun beta => entropyLineFirst L beta lambda)
  let f2 : ℝ → ℝ := fun lambda =>
    signedIntegral mu (fun beta => entropyLineSecond L beta lambda)
  have hIntegral : ∀ lambda ∈ Ioo (-lambda0) lambda0,
      HasDerivAt f0 (f1 lambda) lambda ∧
        HasDerivAt f1 (f2 lambda) lambda := by
    intro lambda hlambda
    have hlambdaClosed : lambda ∈ Icc (-lambda0) lambda0 :=
      ⟨hlambda.1.le, hlambda.2.le⟩
    have hslice0 : Continuous (fun beta : Param => entropyLine L beta lambda) :=
      fullDetailsA11_continuous_param_slice hbundle.1 hlambdaClosed
    have hslice1 : Continuous
        (fun beta : Param => entropyLineFirst L beta lambda) :=
      fullDetailsA11_continuous_param_slice hbundle.2.1 hlambdaClosed
    have hslice2 : Continuous
        (fun beta : Param => entropyLineSecond L beta lambda) :=
      fullDetailsA11_continuous_param_slice hbundle.2.2 hlambdaClosed
    have hstrong0 : ∀ᶠ x in nhds lambda,
        StronglyMeasurable (fun beta => entropyLine L beta x) := by
      filter_upwards [isOpen_Ioo.mem_nhds hlambda] with x hx
      exact (fullDetailsA11_continuous_param_slice hbundle.1
        ⟨hx.1.le, hx.2.le⟩).stronglyMeasurable
    have hstrong1 : ∀ᶠ x in nhds lambda,
        StronglyMeasurable (fun beta => entropyLineFirst L beta x) := by
      filter_upwards [isOpen_Ioo.mem_nhds hlambda] with x hx
      exact (fullDetailsA11_continuous_param_slice hbundle.2.1
        ⟨hx.1.le, hx.2.le⟩).stronglyMeasurable
    have hint0Pos : Integrable (fun beta => entropyLine L beta lambda)
        (signedPos mu) := by
      apply (integrable_const C0).mono hslice0.aestronglyMeasurable
      filter_upwards [] with beta
      exact (hC0 (beta, lambda) ⟨Set.mem_univ beta, hlambdaClosed⟩).trans
        (le_abs_self C0)
    have hint0Neg : Integrable (fun beta => entropyLine L beta lambda)
        (signedNeg mu) := by
      apply (integrable_const C0).mono hslice0.aestronglyMeasurable
      filter_upwards [] with beta
      exact (hC0 (beta, lambda) ⟨Set.mem_univ beta, hlambdaClosed⟩).trans
        (le_abs_self C0)
    have hint1Pos : Integrable
        (fun beta => entropyLineFirst L beta lambda) (signedPos mu) := by
      apply (integrable_const C1).mono hslice1.aestronglyMeasurable
      filter_upwards [] with beta
      exact (hC1 (beta, lambda) ⟨Set.mem_univ beta, hlambdaClosed⟩).trans
        (le_abs_self C1)
    have hint1Neg : Integrable
        (fun beta => entropyLineFirst L beta lambda) (signedNeg mu) := by
      apply (integrable_const C1).mono hslice1.aestronglyMeasurable
      filter_upwards [] with beta
      exact (hC1 (beta, lambda) ⟨Set.mem_univ beta, hlambdaClosed⟩).trans
        (le_abs_self C1)
    have hdiff := signedIntegral_differentiate_twice
      (E := Param)
      (k₀ := fun x beta => entropyLine L beta x)
      (k₁ := fun x beta => entropyLineFirst L beta x)
      (k₂ := fun x beta => entropyLineSecond L beta x)
      (x₀ := lambda) (s := Ioo (-lambda0) lambda0)
      (bound₀ := fun _ => C1) (bound₁ := fun _ => C2) mu
      (isOpen_Ioo.mem_nhds hlambda) hstrong0 hstrong1
      hint0Pos hint0Neg hint1Pos hint1Neg
      hslice1.stronglyMeasurable hslice2.stronglyMeasurable
      (fun beta x hx => hC1 (beta, x)
        ⟨Set.mem_univ beta, ⟨hx.1.le, hx.2.le⟩⟩)
      (fun beta x hx => hC2 (beta, x)
        ⟨Set.mem_univ beta, ⟨hx.1.le, hx.2.le⟩⟩)
      (integrable_const C1) (integrable_const C1)
      (integrable_const C2) (integrable_const C2)
      (fun beta x hx =>
        (fullDetailsA11_hasDerivAt_entropyLine L isOpen_Ioo
          (fun y hy => hpos y ⟨hy.1.le, hy.2.le⟩)
          (fun y hy => hfixed y ⟨hy.1.le, hy.2.le⟩) beta hx).1)
      (fun beta x hx =>
        (fullDetailsA11_hasDerivAt_entropyLine L isOpen_Ioo
          (fun y hy => hpos y ⟨hy.1.le, hy.2.le⟩)
          (fun y hy => hfixed y ⟨hy.1.le, hy.2.le⟩) beta hx).2)
    change
      HasDerivAt
          (fun x => signedIntegral mu (fun beta => entropyLine L beta x))
          (signedIntegral mu (fun beta => entropyLineFirst L beta lambda)) lambda ∧
        HasDerivAt
          (fun x => signedIntegral mu (fun beta => entropyLineFirst L beta x))
          (signedIntegral mu (fun beta => entropyLineSecond L beta lambda)) lambda
    exact hdiff
  have hcont2 : ContinuousOn f2 (Ioo (-lambda0) lambda0) := by
    simpa only [f2] using
      fullDetailsA11_continuousOn_signedIntegral mu hbundle.2.2 C2
        (fun beta lambda hlambda => hC2 (beta, lambda)
          ⟨Set.mem_univ beta, hlambda⟩)
  have hcontDiff : ContDiffOn ℝ 2 f0 (Ioo (-lambda0) lambda0) :=
    fullDetailsA11_contDiffOn_two isOpen_Ioo
      (fun lambda hlambda => (hIntegral lambda hlambda).1)
      (fun lambda hlambda => (hIntegral lambda hlambda).2) hcont2
  refine ⟨by simpa only [f0] using hcontDiff, ?_⟩
  intro lambda hlambda
  have hpair := hIntegral lambda hlambda
  have hfirst : iteratedDeriv (integratedEntropyLine mu L) 1 lambda =
      signedIntegral mu (fun beta => entropyLineFirst L beta lambda) := by
    change deriv f0 lambda = f1 lambda
    exact hpair.1.deriv
  have hderivEventually : deriv f0 =ᶠ[nhds lambda] f1 := by
    filter_upwards [isOpen_Ioo.mem_nhds hlambda] with x hx
    exact (hIntegral x hx).1.deriv
  have hsecond : iteratedDeriv (integratedEntropyLine mu L) 2 lambda =
      signedIntegral mu (fun beta => entropyLineSecond L beta lambda) := by
    change deriv (deriv f0) lambda = f2 lambda
    rw [Filter.EventuallyEq.deriv_eq hderivEventually]
    exact hpair.2.deriv
  simpa only [f0, f1, f2] using ⟨hpair.1, hpair.2, hfirst, hsecond⟩

end ConditionalEntropy
