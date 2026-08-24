import ConditionalEntropy.NecessityMeasureAlgebra

/-!
# Positivity of negative-witness block moments

These elementary integral facts are shared by the temperate and tropical
negative necessity arguments.  They depend only on the signed-witness and
block-moment definitions.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ConditionalEntropy

/-- The upper block moment of the canonical negative witness is strictly
positive whenever the corresponding upper tail has positive mass. -/
theorem upperMoment_negativeSigned_pos_of_tail
    (nu : FiniteMeasure Param) {r : ℝ} (hr : 1 < r)
    (htail : 0 < finiteMeasure nu (Ioi (finiteParam r))) :
    0 < upperMoment (negativeSigned nu) r := by
  have hpositive := upperMoment_positiveSigned_neg_of_tail nu hr htail
  have hneg : upperMoment (negativeSigned nu) r =
      -upperMoment (positiveSigned nu) r := by
    unfold upperMoment positiveSigned
    rw [signedIntegral_negativeSigned, signedIntegral_signedLift]
  rw [hneg]
  exact neg_pos.mpr hpositive

/-- The middle upper cell of a three-block negative witness has a strictly
positive moment whenever it has positive measure. -/
theorem middleMoment_negativeSigned_pos_of_mass
    (nu : FiniteMeasure Param) {a b : ℝ} (ha : 1 < a) (_hab : a < b)
    (hmass : 0 < finiteMeasure nu (Ioo (finiteParam a) (finiteParam b))) :
    0 < threeCellMoment (negativeSigned nu) a b 1 := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  let f : Param → ℝ :=
    (Ioo (finiteParam a) (finiteParam b)).indicator
      (fun beta ↦ -singularWeight beta)
  have hparam : (1 : Param) < finiteParam a := by
    rw [← finiteParam_one]
    change ENNReal.ofReal 1 < ENNReal.ofReal a
    exact (ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans ha)).2 ha
  have hfnonneg : ∀ beta, 0 ≤ f beta := by
    intro beta
    by_cases hbeta : beta ∈ Ioo (finiteParam a) (finiteParam b)
    · simp only [f, Set.indicator_of_mem hbeta]
      exact neg_nonneg.mpr
        (singularWeight_neg_of_one_lt (hparam.trans hbeta.1)).le
    · simp [f, hbeta]
  have hfint : Integrable f (finiteMeasure nu) := by
    have h := (integrable_singularWeight_Ioo_of_gt
      (finiteMeasure nu) (b := b) ha).neg
    apply h.congr
    filter_upwards [] with beta
    by_cases hbeta : beta ∈ Ioo (finiteParam a) (finiteParam b)
    · simp [f, hbeta]
    · simp [f, hbeta]
  have hsupport : Ioo (finiteParam a) (finiteParam b) ⊆ Function.support f := by
    intro beta hbeta
    have hstrict := singularWeight_neg_of_one_lt (hparam.trans hbeta.1)
    simp only [Function.mem_support, f, Set.indicator_of_mem hbeta]
    exact neg_ne_zero.mpr hstrict.ne
  have hsupportMass : 0 < finiteMeasure nu (Function.support f) :=
    hmass.trans_le (measure_mono hsupport)
  have hpos : 0 < ∫ beta, f beta ∂finiteMeasure nu :=
    (integral_pos_iff_support_of_nonneg hfnonneg hfint).2 hsupportMass
  have hcell : threeCellMoment (negativeSigned nu) a b 1 =
      ∫ beta, f beta ∂finiteMeasure nu := by
    rw [threeCellMoment]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Fin.isValue]
    rw [signedIntegral_negativeSigned]
    change -(∫ beta,
      (Ioo (finiteParam a) (finiteParam b)).indicator singularWeight beta
        ∂finiteMeasure nu) = _
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with beta
    by_cases hbeta : beta ∈ Ioo (finiteParam a) (finiteParam b)
    · simp [f, hbeta]
    · simp [f, hbeta]
  rw [hcell]
  exact hpos

/-- The lower truncation of a positive measure is nonnegative. -/
theorem lowerTrunc_nonneg (nu : FiniteMeasure Param) {a : ℝ}
    (_ha : 0 < a) (ha1 : a < 1) : 0 ≤ lowerTrunc nu a := by
  rw [lowerTrunc]
  apply integral_nonneg_of_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Iio] with beta hbeta
  have hbetaOne : beta < (1 : Param) := by
    have haParam : finiteParam a < (1 : Param) := by
      rw [← finiteParam_one]
      change ENNReal.ofReal a < ENNReal.ofReal 1
      exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 ha1
    exact hbeta.trans haParam
  by_cases hbetaZero : beta = 0
  · simp [hbetaZero]
  · exact (singularWeight_pos_of_Ioo
      ⟨lt_of_le_of_ne bot_le (Ne.symm hbetaZero), hbetaOne⟩).le

/-- The upper truncation of a positive measure is nonnegative. -/
theorem upperTrunc_nonneg (nu : FiniteMeasure Param) {b : ℝ}
    (hb : 1 < b) : 0 ≤ upperTrunc nu b := by
  rw [upperTrunc]
  apply integral_nonneg_of_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with beta hbeta
  have hparam : (1 : Param) < finiteParam b := by
    rw [← finiteParam_one]
    change ENNReal.ofReal 1 < ENNReal.ofReal b
    exact (ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans hb)).2 hb
  exact neg_nonneg.mpr
    (singularWeight_neg_of_one_lt (hparam.trans hbeta)).le

end ConditionalEntropy
