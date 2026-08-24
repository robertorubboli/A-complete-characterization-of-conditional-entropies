import ConditionalEntropy.ShannonCurves

/-!
# Signed atoms used by Shannon localization

The atom is defined by the same bounded indicator integral as in the
manuscript.  This file proves that it is the ordinary signed mass of the
singleton and that subtracting the corresponding Dirac signed measure kills
the singleton in total variation.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ConditionalEntropy

/-- The finite point mass used to remove an atom from a signed measure. -/
def diracFinite (a : Param) : FiniteMeasure Param :=
  (diracProb a).toFiniteMeasure

/-- The real signed mass of a singleton, expressed as a signed integral. -/
def signedAtom (mu : SignedMeasure Param) (a : Param) : ℝ :=
  signedIntegral mu (({a} : Set Param).indicator fun _ ↦ 1)

/-- Remove the singleton component of a finite signed measure. -/
def removeSignedAtom (mu : SignedMeasure Param) (a : Param) :
    SignedMeasure Param :=
  mu - signedAtom mu a • signedLift (diracFinite a)

/-- The integral definition of `signedAtom` is exactly signed-measure
evaluation on the measurable singleton. -/
theorem signedAtom_eq_apply (mu : SignedMeasure Param) (a : Param) :
    signedAtom mu a = mu ({a} : Set Param) := by
  unfold signedAtom signedIntegral signedPos signedNeg
  rw [integral_indicator_const 1 (measurableSet_singleton a),
    integral_indicator_const 1 (measurableSet_singleton a)]
  simp only [smul_eq_mul, mul_one]
  calc
    mu.toJordanDecomposition.posPart.real ({a} : Set Param) -
        mu.toJordanDecomposition.negPart.real ({a} : Set Param) =
      mu.toJordanDecomposition.toSignedMeasure ({a} : Set Param) := by
        unfold JordanDecomposition.toSignedMeasure
        rw [Measure.toSignedMeasure_sub_apply (measurableSet_singleton a)]
    _ = mu ({a} : Set Param) := by
      rw [SignedMeasure.toSignedMeasure_toJordanDecomposition]

@[simp] theorem signedLift_diracFinite_apply_singleton (a : Param) :
    signedLift (diracFinite a) ({a} : Set Param) = 1 := by
  unfold signedLift diracFinite diracProb
  rw [Measure.toSignedMeasure_apply_measurable (measurableSet_singleton a)]
  simp [Measure.real]

/-- Evaluation of the atom-removed signed measure on the removed singleton. -/
theorem removeSignedAtom_apply_singleton (mu : SignedMeasure Param) (a : Param) :
    removeSignedAtom mu a ({a} : Set Param) = 0 := by
  rw [removeSignedAtom, _root_.sub_apply,
    _root_.smul_apply, signedLift_diracFinite_apply_singleton, smul_eq_mul,
    mul_one, signedAtom_eq_apply, sub_self]

/-- On a singleton, vanishing of a signed measure forces vanishing of its
total variation. -/
theorem signedTV_singleton_eq_zero_of_apply_eq_zero
    (mu : SignedMeasure Param) (a : Param)
    (hmu : mu ({a} : Set Param) = 0) :
    signedTV mu ({a} : Set Param) = 0 := by
  obtain ⟨S, _hSmeas, hposS, hnegSc⟩ :=
    mu.toJordanDecomposition.mutuallySingular
  have hvalue :
      (signedPos mu).real ({a} : Set Param) -
          (signedNeg mu).real ({a} : Set Param) = 0 := by
    calc
      (signedPos mu).real ({a} : Set Param) -
          (signedNeg mu).real ({a} : Set Param) =
        mu.toJordanDecomposition.toSignedMeasure ({a} : Set Param) := by
          unfold signedPos signedNeg JordanDecomposition.toSignedMeasure
          rw [Measure.toSignedMeasure_sub_apply (measurableSet_singleton a)]
      _ = mu ({a} : Set Param) := by
        rw [SignedMeasure.toSignedMeasure_toJordanDecomposition]
      _ = 0 := hmu
  have hposFinite : signedPos mu ({a} : Set Param) ≠ ∞ :=
    ne_of_lt (measure_lt_top _ _)
  have hnegFinite : signedNeg mu ({a} : Set Param) ≠ ∞ :=
    ne_of_lt (measure_lt_top _ _)
  have hposRealNonneg : 0 ≤ (signedPos mu).real ({a} : Set Param) :=
    ENNReal.toReal_nonneg
  have hnegRealNonneg : 0 ≤ (signedNeg mu).real ({a} : Set Param) :=
    ENNReal.toReal_nonneg
  by_cases haS : a ∈ S
  · have hposAtom : signedPos mu ({a} : Set Param) = 0 := by
      exact measure_mono_null (singleton_subset_iff.mpr haS) hposS
    have hposReal : (signedPos mu).real ({a} : Set Param) = 0 := by
      simp [measureReal_def, hposAtom]
    have hnegReal : (signedNeg mu).real ({a} : Set Param) = 0 := by
      linarith
    have hnegAtom : signedNeg mu ({a} : Set Param) = 0 := by
      apply ((ENNReal.toReal_eq_zero_iff _).mp ?_).resolve_right hnegFinite
      simpa [Measure.real] using hnegReal
    rw [signedTV_eq_add, Measure.add_apply, hposAtom, hnegAtom, add_zero]
  · have haSc : a ∈ Sᶜ := by simp [haS]
    have hnegAtom : signedNeg mu ({a} : Set Param) = 0 := by
      exact measure_mono_null (singleton_subset_iff.mpr haSc) hnegSc
    have hnegReal : (signedNeg mu).real ({a} : Set Param) = 0 := by
      simp [measureReal_def, hnegAtom]
    have hposReal : (signedPos mu).real ({a} : Set Param) = 0 := by
      linarith
    have hposAtom : signedPos mu ({a} : Set Param) = 0 := by
      apply ((ENNReal.toReal_eq_zero_iff _).mp ?_).resolve_right hposFinite
      simpa [Measure.real] using hposReal
    rw [signedTV_eq_add, Measure.add_apply, hposAtom, hnegAtom, add_zero]

/-- Removing the declared signed atom kills its singleton in total
variation. -/
theorem removeSignedAtom_totalVariation_singleton
    (mu : SignedMeasure Param) (a : Param) :
    signedTV (removeSignedAtom mu a) ({a} : Set Param) = 0 :=
  signedTV_singleton_eq_zero_of_apply_eq_zero _ _
    (removeSignedAtom_apply_singleton mu a)

/-! ## Signed-integral linearity for bounded functions -/

private theorem integrable_bounded_signedPart
    (nu : Measure Param) [IsFiniteMeasure nu]
    (f : Param → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) : Integrable f nu := by
  apply Integrable.of_bound hf.aestronglyMeasurable C
  exact ae_of_all nu fun x ↦ by
    simpa only [Real.norm_eq_abs] using hC x

/-- Exact bounded-integral decomposition after removing an atom. -/
theorem signedIntegral_removeSignedAtom
    (mu : SignedMeasure Param) (a : Param) (f : Param → ℝ)
    (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) :
    signedIntegral mu f =
      signedAtom mu a * f a + signedIntegral (removeSignedAtom mu a) f := by
  let mu0 := removeSignedAtom mu a
  let m := signedAtom mu a
  let delta := signedLift (diracFinite a)
  have hmuPos : Integrable f (signedPos mu) :=
    integrable_bounded_signedPart (signedPos mu) f hf C hC
  have hmuNeg : Integrable f (signedNeg mu) :=
    integrable_bounded_signedPart (signedNeg mu) f hf C hC
  have hmu0Pos : Integrable f (signedPos mu0) :=
    integrable_bounded_signedPart (signedPos mu0) f hf C hC
  have hmu0Neg : Integrable f (signedNeg mu0) :=
    integrable_bounded_signedPart (signedNeg mu0) f hf C hC
  have hmuPosV : (signedPos mu).toSignedMeasure.Integrable f := by
    simpa [VectorMeasure.Integrable] using hmuPos
  have hmuNegV : (signedNeg mu).toSignedMeasure.Integrable f := by
    simpa [VectorMeasure.Integrable] using hmuNeg
  have hmuV : mu.Integrable f := by
    rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition mu]
    unfold JordanDecomposition.toSignedMeasure
    exact hmuPosV.sub_vectorMeasure hmuNegV
  have hdeltaM : Integrable f (diracFinite a : Measure Param) :=
    integrable_bounded_signedPart (diracFinite a : Measure Param) f hf C hC
  have hdeltaV : delta.Integrable f := by
    dsimp only [delta]
    unfold signedLift
    simpa [VectorMeasure.Integrable] using hdeltaM
  have hvector :
      vectorSignedIntegral mu0 f =
        vectorSignedIntegral mu f - m * f a := by
    have hmu0 : mu0 = mu - m • delta := by
      rfl
    rw [hmu0]
    unfold vectorSignedIntegral
    rw [VectorMeasure.integral_sub_vectorMeasure hmuV
        (hdeltaV.smul_vectorMeasure m),
      VectorMeasure.integral_smul_vectorMeasure]
    have hdelta : ∫ᵛ x, f x ∂<•delta = f a := by
      dsimp only [delta]
      unfold signedLift diracFinite diracProb
      rw [VectorMeasure.integral_toSignedMeasure]
      change (∫ x, f x ∂Measure.dirac a) = f a
      rw [integral_dirac]
    rw [hdelta]
    rfl
  rw [signedIntegral_eq_vectorSignedIntegral_of_integrable mu f hmuPos hmuNeg,
    signedIntegral_eq_vectorSignedIntegral_of_integrable mu0 f hmu0Pos hmu0Neg]
  dsimp only [m] at hvector ⊢
  rw [hvector]
  ring

/-- Literal conjunction used by the Shannon localization proof. -/
theorem removeSignedAtom_spec (mu : SignedMeasure Param) (a : Param) :
    signedTV (removeSignedAtom mu a) ({a} : Set Param) = 0 ∧
      ∀ f : Param → ℝ, Measurable f →
        (∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C) →
        signedIntegral mu f =
          signedAtom mu a * f a +
            signedIntegral (removeSignedAtom mu a) f := by
  refine ⟨removeSignedAtom_totalVariation_singleton mu a, ?_⟩
  intro f hf hbound
  obtain ⟨C, _hC0, hC⟩ := hbound
  exact signedIntegral_removeSignedAtom mu a f hf C hC

end ConditionalEntropy
