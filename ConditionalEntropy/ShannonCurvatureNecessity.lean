import ConditionalEntropy.CurvatureObstructions
import ConditionalEntropy.ShannonCurveKernelBridge
import ConditionalEntropy.ShannonWitnessBridge
import ConditionalEntropy.ULiftInvariance

/-!
# Curvature obstructions for the dedicated Shannon curves

This file separates the local scalar-curvature argument from the later
localization theorem.  Once logarithmic-kernel limits are known, the two
public lemmas below turn the wrong limiting curvature sign into an immediate
contradiction with the global positive/negative column shape.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

private theorem shannonLogKernelLimitPackage
    (mu : SignedMeasure Param) (theta : ShannonData) (z : ℝ × ℝ)
    (a b : ℝ)
    (hfirst : Tendsto
      (fun n ↦ shannonLogKernel mu theta n z 1) atTop (𝓝 a))
    (hsecond : Tendsto
      (fun n ↦ shannonLogKernel mu theta n z 2) atTop (𝓝 b)) :
    let phi : ℕ → ℝ → ℝ := fun n lambda ↦
      shannonPhiCurve mu theta n z lambda
    (∀ n, ∃ epsilon : ℝ, 0 < epsilon ∧ 0 < phi n 0 ∧
      ContDiffOn ℝ 2 (phi n) (Ioo (-epsilon) epsilon)) ∧
    Tendsto (fun n ↦ deriv (fun lambda ↦ Real.log (phi n lambda)) 0)
      atTop (𝓝 a) ∧
    Tendsto
      (fun n ↦ secondDeriv (fun lambda ↦ Real.log (phi n lambda)) 0)
      atTop (𝓝 b) := by
  dsimp only
  let phi : ℕ → ℝ → ℝ := fun n lambda ↦
    shannonPhiCurve mu theta n z lambda
  have hsmooth : ∀ n, ∃ epsilon : ℝ, 0 < epsilon ∧ 0 < phi n 0 ∧
      ContDiffOn ℝ 2 (phi n) (Ioo (-epsilon) epsilon) := by
    intro n
    obtain ⟨epsilon, hepsilon, _hpos, hphi0, hdiff, _hGdiff,
      _hlog, _hG⟩ := shannonCurveKernelBridge mu theta n z
    exact ⟨epsilon, hepsilon, hphi0, by simpa only [phi] using hdiff⟩
  have hfirstEq : ∀ n,
      deriv (fun lambda ↦ Real.log (phi n lambda)) 0 =
        shannonLogKernel mu theta n z 1 := by
    intro n
    obtain ⟨_epsilon, _hepsilon, _hpos, _hphi0, _hdiff, _hGdiff,
      hlog, _hG⟩ := shannonCurveKernelBridge mu theta n z
    have h := hlog 1 (by norm_num)
    change deriv
      (fun lambda ↦ Real.log
        (shannonPhiCurve mu theta n z lambda)) 0 =
          shannonLogKernel mu theta n z 1 at h
    simpa only [phi] using h
  have hsecondEq : ∀ n,
      secondDeriv (fun lambda ↦ Real.log (phi n lambda)) 0 =
        shannonLogKernel mu theta n z 2 := by
    intro n
    obtain ⟨_epsilon, _hepsilon, _hpos, _hphi0, _hdiff, _hGdiff,
      hlog, _hG⟩ := shannonCurveKernelBridge mu theta n z
    have h := hlog 2 (by norm_num)
    change secondDeriv
      (fun lambda ↦ Real.log
        (shannonPhiCurve mu theta n z lambda)) 0 =
          shannonLogKernel mu theta n z 2 at h
    simpa only [phi] using h
  refine ⟨hsmooth, ?_, ?_⟩
  · exact hfirst.congr'
      (Filter.Eventually.of_forall fun n ↦ (hfirstEq n).symm)
  · exact hsecond.congr'
      (Filter.Eventually.of_forall fun n ↦ (hsecondEq n).symm)

/-- A Shannon logarithmic-kernel limit with positive normalized curvature
contradicts concavity of the positive signed column. -/
theorem positiveShannonCurvatureContradiction
    (nu : FiniteMeasure Param) (hconc : PosPhiConcave.{u} nu)
    (theta : ShannonData) (z : ℝ × ℝ) (a b : ℝ)
    (hfirst : Tendsto
      (fun n ↦ shannonLogKernel (positiveSigned nu) theta n z 1)
      atTop (𝓝 a))
    (hsecond : Tendsto
      (fun n ↦ shannonLogKernel (positiveSigned nu) theta n z 2)
      atTop (𝓝 b))
    (hcurv : 0 < b + a ^ 2) : False := by
  let phi : ℕ → ℝ → ℝ := fun n lambda ↦
    shannonPhiCurve (positiveSigned nu) theta n z lambda
  have H := shannonLogKernelLimitPackage
    (positiveSigned nu) theta z a b hfirst hsecond
  dsimp only at H
  have hlineConcave : ∀ n, ∃ epsilon : ℝ, 0 < epsilon ∧
      ConcaveOn ℝ (Ioo (-epsilon) epsilon) (phi n) := by
    intro n
    obtain ⟨epsilon, hepsilon, hpos, _hphi0, _hdiff, _hGdiff,
      _hlog, _hG⟩ := shannonCurveKernelBridge
        (positiveSigned nu) theta n z
    letI := shannonIndexNonempty theta n
    have hconeLift : ConcaveCone
        (PhiSigned (positiveSigned nu) :
          ConeVec (ULift.{u} (ShannonIndex theta n)) → ℝ) := hconc
    have hcone : ConcaveCone
        (PhiSigned (positiveSigned nu) : ConeVec (ShannonIndex theta n) → ℝ) := by
      exact concaveCone_PhiSigned_of_ulift (positiveSigned nu) hconeLift
    have hline :=
      (coneAffineLineBridge (shannonLineData theta n z)
        (Ioo (-epsilon) epsilon) (convex_Ioo (-epsilon) epsilon) hpos
        (PhiSigned (positiveSigned nu))).1 hcone
    refine ⟨epsilon, hepsilon, ?_⟩
    simpa only [phi, shannonPhiCurve] using hline
  exact (typedLogCurvatureContradiction phi a b H.1 H.2.1 H.2.2).1
    hcurv hlineConcave

/-- A Shannon logarithmic-kernel limit with negative normalized curvature
contradicts convexity of the negative signed column. -/
theorem negativeShannonCurvatureContradiction
    (nu : FiniteMeasure Param) (hconv : NegPhiConvex.{u} nu)
    (theta : ShannonData) (z : ℝ × ℝ) (a b : ℝ)
    (hfirst : Tendsto
      (fun n ↦ shannonLogKernel (negativeSigned nu) theta n z 1)
      atTop (𝓝 a))
    (hsecond : Tendsto
      (fun n ↦ shannonLogKernel (negativeSigned nu) theta n z 2)
      atTop (𝓝 b))
    (hcurv : b + a ^ 2 < 0) : False := by
  let phi : ℕ → ℝ → ℝ := fun n lambda ↦
    shannonPhiCurve (negativeSigned nu) theta n z lambda
  have H := shannonLogKernelLimitPackage
    (negativeSigned nu) theta z a b hfirst hsecond
  dsimp only at H
  have hlineConvex : ∀ n, ∃ epsilon : ℝ, 0 < epsilon ∧
      ConvexOn ℝ (Ioo (-epsilon) epsilon) (phi n) := by
    intro n
    obtain ⟨epsilon, hepsilon, hpos, _hphi0, _hdiff, _hGdiff,
      _hlog, _hG⟩ := shannonCurveKernelBridge
        (negativeSigned nu) theta n z
    letI := shannonIndexNonempty theta n
    have hconeLift : ConvexCone
        (PhiSigned (negativeSigned nu) :
          ConeVec (ULift.{u} (ShannonIndex theta n)) → ℝ) := hconv
    have hcone : ConvexCone
        (PhiSigned (negativeSigned nu) : ConeVec (ShannonIndex theta n) → ℝ) := by
      exact convexCone_PhiSigned_of_ulift (negativeSigned nu) hconeLift
    have hline :=
      (coneAffineLineBridge (shannonLineData theta n z)
        (Ioo (-epsilon) epsilon) (convex_Ioo (-epsilon) epsilon) hpos
        (PhiSigned (negativeSigned nu))).2 hcone
    refine ⟨epsilon, hepsilon, ?_⟩
    simpa only [phi, shannonPhiCurve] using hline
  exact (typedLogCurvatureContradiction phi a b H.1 H.2.1 H.2.2).2
    hcurv hlineConvex

end ConditionalEntropy
