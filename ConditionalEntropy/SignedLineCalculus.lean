import ConditionalEntropy.EndpointLineCalculus
import ConditionalEntropy.SignedWitnesses

/-!
# Signed entropy integrals along positive lines

This module connects the endpoint-aware line calculus to the signed column
functions used in the necessity proof.  All integrals are the Jordan signed
integrals from `ParamMeasure`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

section

variable {I : Type u} [Fintype I] [Nonempty I]

/-- Endpoint-aware Renyi entropy integrated against a finite signed measure
along a total positive line. -/
def integratedEntropyLine (mu : SignedMeasure Param)
    (L : PositiveLineData I) (lambda : ℝ) : ℝ :=
  signedIntegral mu (fun a => entropyLine L a lambda)

/-- The logarithm of the signed exponential column function along a positive
line, written in the additive form used for differentiation. -/
def signedLogPhiLine (mu : SignedMeasure Param)
    (L : PositiveLineData I) (lambda : ℝ) : ℝ :=
  Real.log (lineMass L lambda) + integratedEntropyLine mu L lambda

omit [Nonempty I] in
theorem l1Mass_lineCone (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) :
    l1Mass (lineCone L lambda h).1 = lineMass L lambda := by
  rfl

theorem normalize_linePosCone (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) :
    normalize (linePosCone L lambda h) = lineProb L lambda := by
  exact (lineProb_of_positive L lambda h).symm

/-- Exact bridge from the total line wrappers to the signed column functions.
This is the literal conjunction used by all block and Shannon curves. -/
theorem signedLineColumnBridge (mu : SignedMeasure Param)
    (L : PositiveLineData I) {lambda : ℝ} (h : LinePositive L lambda) :
    lineProb L lambda = normalize (linePosCone L lambda h) ∧
      integratedEntropyLine mu L lambda =
        GSigned mu (linePosCone L lambda h) ∧
      0 < PhiSigned mu (lineCone L lambda h) ∧
      signedLogPhiLine mu L lambda =
        Real.log (PhiSigned mu (lineCone L lambda h)) ∧
      lineConeTotal L lambda = lineCone L lambda h ∧
      linePosConeTotal L lambda = linePosCone L lambda h := by
  have hprob := lineProb_of_positive L lambda h
  have hmass : 0 < lineMass L lambda := lineMass_pos L h
  have hcone : lineCone L lambda h ≠ 0 := by
    intro hz
    have hzMass : l1Mass (lineCone L lambda h).1 = 0 := by
      rw [hz]
      simp [l1Mass]
    rw [l1Mass_lineCone L h] at hzMass
    exact hmass.ne' hzMass
  have hIntegrated : integratedEntropyLine mu L lambda =
      GSigned mu (linePosCone L lambda h) := by
    unfold integratedEntropyLine GSigned integratedEntropySigned entropyLine
    rw [hprob]
  have hPosConeEq :
      toPosCone (lineCone L lambda h) hcone = linePosCone L lambda h := by
    apply Subtype.ext
    rfl
  have hPhi : PhiSigned mu (lineCone L lambda h) =
      lineMass L lambda * Real.exp (integratedEntropyLine mu L lambda) := by
    rw [PhiSigned_of_ne mu (lineCone L lambda h) hcone]
    rw [l1Mass_lineCone L h]
    unfold integratedEntropyLine integratedEntropySigned entropyLine
    rw [hPosConeEq, normalize_linePosCone L h]
  have hPhiPos : 0 < PhiSigned mu (lineCone L lambda h) := by
    rw [hPhi]
    exact mul_pos hmass (Real.exp_pos _)
  have hLog : signedLogPhiLine mu L lambda =
      Real.log (PhiSigned mu (lineCone L lambda h)) := by
    rw [hPhi, Real.log_mul hmass.ne' (Real.exp_pos _).ne', Real.log_exp]
    rfl
  exact ⟨hprob, hIntegrated, hPhiPos, hLog,
    lineConeTotal_of_positive L lambda h,
    linePosConeTotal_of_positive L lambda h⟩

/-! ## Algebraic closure of differentiated signed integrals -/

/-- Once the two signed-integral derivative identities have been established
on an open positive interval, the first two iterated derivatives of the
logarithmic column line split exactly into the log-mass and entropy-integral
terms.  This theorem contains no analytic assumption beyond the two genuine
`HasDerivAt` facts that the dominated-integral argument must supply. -/
theorem signedLogPhiLineDerivativesOfIntegral
    (mu : SignedMeasure Param) (L : PositiveLineData I)
    {U : Set ℝ} (hU : IsOpen U)
    (hpos : ∀ lambda ∈ U, LinePositive L lambda)
    (hIntegral : ∀ lambda ∈ U,
      HasDerivAt (integratedEntropyLine mu L)
        (signedIntegral mu (fun a => entropyLineFirst L a lambda)) lambda ∧
      HasDerivAt
        (fun s => signedIntegral mu (fun a => entropyLineFirst L a s))
        (signedIntegral mu (fun a => entropyLineSecond L a lambda)) lambda)
    {lambda : ℝ} (hlambda : lambda ∈ U) :
    HasDerivAt (integratedEntropyLine mu L)
        (signedIntegral mu (fun a => entropyLineFirst L a lambda)) lambda ∧
      HasDerivAt
        (fun s => signedIntegral mu (fun a => entropyLineFirst L a s))
        (signedIntegral mu (fun a => entropyLineSecond L a lambda)) lambda ∧
      iteratedDeriv (signedLogPhiLine mu L) 1 lambda =
        deriv (fun s => Real.log (lineMass L s)) lambda +
          signedIntegral mu (fun a => entropyLineFirst L a lambda) ∧
      iteratedDeriv (signedLogPhiLine mu L) 2 lambda =
        secondDeriv (fun s => Real.log (lineMass L s)) lambda +
          signedIntegral mu (fun a => entropyLineSecond L a lambda) := by
  let firstIntegral : ℝ → ℝ := fun s =>
    signedIntegral mu (fun a => entropyLineFirst L a s)
  let secondIntegral : ℝ → ℝ := fun s =>
    signedIntegral mu (fun a => entropyLineSecond L a s)
  have hp := hpos lambda hlambda
  have hInt := hIntegral lambda hlambda
  have hLogMass := hasDerivAt_log_lineMass L hp
  have hSignedLogEq : signedLogPhiLine mu L =
      (fun s => Real.log (lineMass L s)) + integratedEntropyLine mu L := by
    funext s
    rfl
  have hFirst : HasDerivAt (signedLogPhiLine mu L)
      (escortMean L 1 lambda + firstIntegral lambda) lambda := by
    rw [hSignedLogEq]
    simpa only [firstIntegral] using hLogMass.add hInt.1
  have hFirstValue : iteratedDeriv (signedLogPhiLine mu L) 1 lambda =
      escortMean L 1 lambda + firstIntegral lambda := by
    simpa [iteratedDeriv] using hFirst.deriv
  have hDerivLogMass : deriv (fun s => Real.log (lineMass L s)) lambda =
      escortMean L 1 lambda := hLogMass.deriv
  have hMean := hasDerivAt_escortMean L (a := (1 : ℝ)) zero_lt_one hp
  have hMeanClosed : HasDerivAt (escortMean L 1)
      (-(escortMean L 1 lambda) ^ 2) lambda := by
    convert hMean using 1
    ring
  have hClosedSecond : HasDerivAt
      (fun s => escortMean L 1 s + firstIntegral s)
      (-(escortMean L 1 lambda) ^ 2 + secondIntegral lambda) lambda := by
    exact hMeanClosed.add hInt.2
  have hDerivEventually : deriv (signedLogPhiLine mu L) =ᶠ[𝓝 lambda]
      fun s => escortMean L 1 s + firstIntegral s := by
    filter_upwards [hU.mem_nhds hlambda] with s hs
    have hsFirst : HasDerivAt (signedLogPhiLine mu L)
        (escortMean L 1 s + firstIntegral s) s := by
      rw [hSignedLogEq]
      simpa only [firstIntegral] using
        (hasDerivAt_log_lineMass L (hpos s hs)).add (hIntegral s hs).1
    exact hsFirst.deriv
  have hSecond : HasDerivAt (deriv (signedLogPhiLine mu L))
      (-(escortMean L 1 lambda) ^ 2 + secondIntegral lambda) lambda :=
    hClosedSecond.congr_of_eventuallyEq hDerivEventually
  have hSecondValue : iteratedDeriv (signedLogPhiLine mu L) 2 lambda =
      -(escortMean L 1 lambda) ^ 2 + secondIntegral lambda := by
    simpa [iteratedDeriv] using hSecond.deriv
  have hSecondLogMass : secondDeriv (fun s => Real.log (lineMass L s)) lambda =
      -(escortMean L 1 lambda) ^ 2 := by
    unfold secondDeriv
    have hLogEventually : deriv (fun s => Real.log (lineMass L s)) =ᶠ[𝓝 lambda]
        escortMean L 1 := by
      filter_upwards [hU.mem_nhds hlambda] with s hs
      exact (hasDerivAt_log_lineMass L (hpos s hs)).deriv
    exact (hMeanClosed.congr_of_eventuallyEq hLogEventually).deriv
  refine ⟨hInt.1, hInt.2, ?_, ?_⟩
  · rw [hFirstValue, hDerivLogMass]
  · rw [hSecondValue, hSecondLogMass]

end

end ConditionalEntropy
