import ConditionalEntropy.ShannonAlgebra

/-!
# Scalar curves for the Shannon localization family

This file records the exact bridges between the total line wrappers and the
signed column curves, together with the finite logarithmic-mass calculus used
in the Shannon localization argument.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

/-- On a positive part of the Shannon line, the total norm-free curve is the
signed integral of the endpoint-aware Renyi entropy. -/
theorem shannonGCurve_of_positive (mu : SignedMeasure Param)
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) {lambda : ℝ}
    (h : LinePositive (shannonLineData theta n z) lambda) :
    letI := shannonIndexNonempty theta n
    shannonGCurve mu theta n z lambda =
      integratedEntropyLine mu (shannonLineData theta n z) lambda := by
  letI := shannonIndexNonempty theta n
  have hb := signedLineColumnBridge mu (shannonLineData theta n z) h
  unfold shannonGCurve
  rw [hb.2.2.2.2.2]
  exact hb.2.1.symm

/-- The total signed exponential Shannon curve is positive on every positive
part of the underlying line. -/
theorem shannonPhiCurve_pos_of_positive (mu : SignedMeasure Param)
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) {lambda : ℝ}
    (h : LinePositive (shannonLineData theta n z) lambda) :
    0 < shannonPhiCurve mu theta n z lambda := by
  letI := shannonIndexNonempty theta n
  have hb := signedLineColumnBridge mu (shannonLineData theta n z) h
  unfold shannonPhiCurve
  rw [hb.2.2.2.2.1]
  exact hb.2.2.1

/-- On a positive part of the Shannon line, the logarithm of the total
exponential curve is the additive logarithmic entropy line. -/
theorem log_shannonPhiCurve_of_positive (mu : SignedMeasure Param)
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) {lambda : ℝ}
    (h : LinePositive (shannonLineData theta n z) lambda) :
    letI := shannonIndexNonempty theta n
    Real.log (shannonPhiCurve mu theta n z lambda) =
      signedLogPhiLine mu (shannonLineData theta n z) lambda := by
  letI := shannonIndexNonempty theta n
  have hb := signedLineColumnBridge mu (shannonLineData theta n z) h
  unfold shannonPhiCurve
  rw [hb.2.2.2.2.1]
  exact hb.2.2.2.1.symm

theorem shannonPhiCurve_zero_pos (mu : SignedMeasure Param)
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) :
    0 < shannonPhiCurve mu theta n z 0 :=
  shannonPhiCurve_pos_of_positive mu theta n z (linePositiveZero _)

/-- The declared Shannon mass is definitionally the mass of its positive
line data. -/
theorem shannonMass_eq_lineMass (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (lambda : ℝ) :
    shannonMass theta n z lambda =
      lineMass (shannonLineData theta n z) lambda := by
  rfl

/-- Exact expansion of the raw Shannon mass into its three blocks. -/
theorem shannonMass_eq_sum (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (lambda : ℝ) :
    shannonMass theta n z lambda =
      ∑ j : Fin 3, (shannonCount theta n j : ℝ) *
        shannonBase theta n z (shannonRepresentative theta n j) *
          (1 + shannonBlockVelocity theta n z j * lambda) := by
  change (∑ i : Σ j : Fin 3, Fin (shannonCount theta n j),
      shannonBase theta n z i *
        (1 + shannonVelocity theta n z i * lambda)) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ _i : Fin (shannonCount theta n j),
      shannonBase theta n z (shannonRepresentative theta n j) *
        (1 + shannonBlockVelocity theta n z j * lambda)) = _
  simp
  ring

/-- First derivative of the logarithmic Shannon mass at the base point. -/
theorem shannonLogMassKernel_one (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) :
    shannonLogMassKernel theta n z 1 = shannonMean theta n z 1 := by
  letI := shannonIndexNonempty theta n
  unfold shannonLogMassKernel
  change deriv (fun lambda ↦
      Real.log (lineMass (shannonLineData theta n z) lambda)) 0 = _
  rw [(hasDerivAt_log_lineMass (shannonLineData theta n z)
    (linePositiveZero _)).deriv, escortMean_shannonLine_zero]

/-- Second derivative of the logarithmic Shannon mass at the base point. -/
theorem shannonLogMassKernel_two (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) :
    shannonLogMassKernel theta n z 2 =
      -(shannonMean theta n z 1) ^ 2 := by
  letI := shannonIndexNonempty theta n
  unfold shannonLogMassKernel
  change secondDeriv (fun lambda ↦
    Real.log (lineMass (shannonLineData theta n z) lambda)) 0 = _
  unfold secondDeriv
  let L := shannonLineData theta n z
  have hposNhd : ∀ᶠ lambda in nhds (0 : ℝ), LinePositive L lambda :=
    (isOpen_setOf_linePositive L).mem_nhds (linePositiveZero L)
  have hderiv : deriv (fun lambda ↦ Real.log (lineMass L lambda)) =ᶠ[nhds 0]
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
    escortMean_shannonLine_zero]

/-- The square relation in the logarithmic-mass part of the Shannon
localization is exact at every finite scale. -/
theorem shannonLogMassKernel_two_eq_neg_sq (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) :
    shannonLogMassKernel theta n z 2 =
      -shannonLogMassKernel theta n z 1 ^ 2 := by
  rw [shannonLogMassKernel_one, shannonLogMassKernel_two]

end ConditionalEntropy
