import ConditionalEntropy.SignedWitnesses
import ConditionalEntropy.BlockLocalization

/-!
# Measure algebra for the necessity witnesses

This module supplies the positive lower and upper truncations used in the
negative-temperate necessity argument and identifies them with the signed
block moments of the canonical negative witness.
-/

noncomputable section

open MeasureTheory Set

namespace ConditionalEntropy

/-- Integration against the canonical negative witness is negated positive
integration. -/
theorem signedIntegral_negativeSigned (nu : FiniteMeasure Param)
    (f : Param → ℝ) :
    signedIntegral (negativeSigned nu) f =
      -(∫ x, f x ∂(nu : Measure Param)) := by
  unfold negativeSigned signedIntegral signedPos signedNeg
  rw [SignedMeasure.toJordanDecomposition_neg,
    JordanDecomposition.neg_posPart, JordanDecomposition.neg_negPart]
  change (∫ x, f x ∂signedNeg (signedLift nu)) -
    (∫ x, f x ∂signedPos (signedLift nu)) = _
  rw [signedNeg_signedLift, signedPos_signedLift]
  simp

/-- Positive lower truncation of the singular kernel for a finite positive
measure. -/
def lowerTrunc (nu : FiniteMeasure Param) (r : ℝ) : ℝ :=
  ∫ beta in Iio (finiteParam r), singularWeight beta
    ∂finiteMeasure nu

/-- Positive upper truncation, written with the nonnegative kernel
`-singularWeight` on the upper cell. -/
def upperTrunc (nu : FiniteMeasure Param) (r : ℝ) : ℝ :=
  ∫ beta in Ioi (finiteParam r), -singularWeight beta
    ∂finiteMeasure nu

/-- The signed lower and upper block moments of a negative witness are the
negated lower truncation and the positive upper truncation, respectively
(`lem:negative-truncation-bridge`). -/
theorem negativeTruncationBridge (nu : FiniteMeasure Param) :
    (∀ a : ℝ, 0 < a → a < 1 →
      lowerMoment (negativeSigned nu) a = -lowerTrunc nu a) ∧
    (∀ b : ℝ, 1 < b →
      upperMoment (negativeSigned nu) b = upperTrunc nu b) := by
  constructor
  · intro a _ha _ha1
    rw [lowerMoment, signedIntegral_negativeSigned, lowerTrunc]
    rw [integral_indicator measurableSet_Iio]
    rfl
  · intro b _hb1
    rw [upperMoment, signedIntegral_negativeSigned, upperTrunc]
    rw [integral_indicator measurableSet_Ioi, integral_neg]
    rfl

/-- A positive witness has a strictly negative upper block moment whenever
the corresponding upper tail has positive mass. -/
theorem upperMoment_positiveSigned_neg_of_tail
    (nu : FiniteMeasure Param) {r : ℝ} (hr : 1 < r)
    (htail : 0 < finiteMeasure nu (Ioi (finiteParam r))) :
    upperMoment (positiveSigned nu) r < 0 := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  let f : Param → ℝ :=
    (Ioi (finiteParam r)).indicator (fun beta ↦ -singularWeight beta)
  have hparam : (1 : Param) < finiteParam r := by
    rw [← finiteParam_one]
    change ENNReal.ofReal 1 < ENNReal.ofReal r
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans zero_lt_one hr)).2 hr
  have hfnonneg : ∀ beta, 0 ≤ f beta := by
    intro beta
    by_cases hbeta : beta ∈ Ioi (finiteParam r)
    · simp only [f, Set.indicator_of_mem hbeta]
      exact neg_nonneg.mpr
        (singularWeight_neg_of_one_lt (hparam.trans hbeta)).le
    · simp [f, hbeta]
  have hfint : Integrable f (finiteMeasure nu) := by
    have h := (integrable_singularWeight_Ioi
      (finiteMeasure nu) hr).neg
    apply h.congr
    filter_upwards [] with beta
    by_cases hbeta : beta ∈ Ioi (finiteParam r)
    · simp [f, hbeta]
    · simp [f, hbeta]
  have hsupport : Ioi (finiteParam r) ⊆ Function.support f := by
    intro beta hbeta
    have hneg := singularWeight_neg_of_one_lt (hparam.trans hbeta)
    simp only [Function.mem_support]
    simp only [f, Set.indicator_of_mem hbeta]
    exact neg_ne_zero.mpr hneg.ne
  have hsupportMass : 0 < finiteMeasure nu (Function.support f) :=
    htail.trans_le (measure_mono hsupport)
  have hpos : 0 < ∫ beta, f beta ∂finiteMeasure nu :=
    (integral_pos_iff_support_of_nonneg hfnonneg hfint).2 hsupportMass
  have hfneg : f = fun beta ↦
      -((Ioi (finiteParam r)).indicator singularWeight beta) := by
    funext beta
    by_cases hbeta : beta ∈ Ioi (finiteParam r) <;> simp [f, hbeta]
  rw [hfneg, integral_neg] at hpos
  rw [upperMoment, positiveSigned, signedIntegral_signedLift]
  exact neg_pos.mp hpos

end ConditionalEntropy
