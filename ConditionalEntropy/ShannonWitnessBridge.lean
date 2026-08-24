import ConditionalEntropy.ShannonLocalizationTargets

/-!
# Positive Shannon witnesses and their lower singular moment

This file completes the literal witness bridge used at the Shannon point.
The lower truncation stays inside the finite interval below `1`, where the
real singular coefficient is nonnegative and agrees with `omegaLower`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ConditionalEntropy

private theorem omegaLower_toReal_eq_singularWeight_of_lt
    {r : ℝ} (_hr : 0 < r) (hr1 : r < 1) {a : Param}
    (ha : a < finiteParam r) :
    (omegaLower a).toReal = singularWeight a := by
  have hrParam : finiteParam r < (1 : Param) := by
    exact ENNReal.ofReal_lt_one.mpr hr1
  have ha1 : a < (1 : Param) := lt_trans ha hrParam
  have hatop : a ≠ (⊤ : Param) := ne_top_of_lt ha1
  have hreal1 : ENNReal.toReal a < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hatop ENNReal.one_ne_top).mpr ha1
  have hreal0 : 0 ≤ ENNReal.toReal a := ENNReal.toReal_nonneg
  have hrealne : ENNReal.toReal a ≠ 1 := ne_of_lt hreal1
  have hden : 0 ≤ 1 - ENNReal.toReal a := sub_nonneg.mpr hreal1.le
  have hquot : 0 ≤ ENNReal.toReal a / (1 - ENNReal.toReal a) :=
    div_nonneg hreal0 hden
  have hsing :
      singularWeight a = ENNReal.toReal a / (1 - ENNReal.toReal a) := by
    rw [singularWeight]
    simp only [hatop, ↓reduceDIte, paramToReal, hrealne, if_false]
  rw [omegaLower, if_pos ⟨bot_le, ha1⟩, hsing,
    ENNReal.toReal_ofReal hquot]

/-- On every strict finite truncation below one, the lower singular kernel
is the `ENNReal` lift of the manuscript's real singular coefficient. -/
theorem lowerSingularKernelBridge {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∀ a ∈ Iio (finiteParam r),
      (omegaLower a).toReal = singularWeight a := by
  intro a ha
  exact omegaLower_toReal_eq_singularWeight_of_lt hr hr1 ha

/-- Literal atom and positive-lower-truncation bridge from the manuscript. -/
theorem signedWitnessIntegralBridge (nu : FiniteMeasure Param) :
    (∀ a : Param, signedAtom (positiveSigned nu) a =
      ENNReal.toReal (finiteMeasure nu ({a} : Set Param))) ∧
    (∀ a : Param, signedAtom (negativeSigned nu) a =
      -ENNReal.toReal (finiteMeasure nu ({a} : Set Param))) ∧
    (∀ r : ℝ, 0 < r → r < 1 →
      lowerMoment (positiveSigned nu) r =
        ENNReal.toReal
          (∫⁻ a in Iio (finiteParam r), omegaLower a ∂finiteMeasure nu)) := by
  refine ⟨signedAtom_positiveSigned nu, signedAtom_negativeSigned nu, ?_⟩
  intro r hr hr1
  let rho : Measure Param := finiteMeasure nu
  let s : Set Param := Iio (finiteParam r)
  have hs : MeasurableSet s := measurableSet_Iio
  have htoReal :
      ∫ a in s, (omegaLower a).toReal ∂rho =
        ENNReal.toReal (∫⁻ a in s, omegaLower a ∂rho) := by
    exact integral_toReal measurable_omegaLower.aemeasurable
      (ae_of_all _ fun a ↦ omegaLower_lt_top a)
  calc
    lowerMoment (positiveSigned nu) r =
        ∫ a in s, singularWeight a ∂rho := by
      simp only [lowerMoment, positiveSigned, signedIntegral_signedLift]
      exact integral_indicator hs
    _ = ∫ a in s, (omegaLower a).toReal ∂rho := by
      apply setIntegral_congr_fun hs
      intro a ha
      exact (lowerSingularKernelBridge hr hr1 a ha).symm
    _ = ENNReal.toReal (∫⁻ a in s, omegaLower a ∂rho) := htoReal
    _ = ENNReal.toReal
        (∫⁻ a in Iio (finiteParam r), omegaLower a ∂finiteMeasure nu) := rfl

end ConditionalEntropy
