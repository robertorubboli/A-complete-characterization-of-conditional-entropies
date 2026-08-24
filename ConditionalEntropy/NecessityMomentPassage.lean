import ConditionalEntropy.NullThresholds
import ConditionalEntropy.NecessityMeasureAlgebra
import ConditionalEntropy.ShannonWitnessBridge

/-!
# Positive-measure passage from null truncations to the full lower moment

Necessity arguments first obtain bounds at atom-free thresholds below one.
This module packages the common monotone-convergence step for the positive
underlying measure.  No convergence statement for a signed measure is used.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace ConditionalEntropy

/-- Every lower singular integral truncated strictly below one is finite. -/
theorem lowerTruncatedLIntegral_lt_top (nu : FiniteMeasure Param)
    {r : ℝ} (_hr : 0 < r) (hr1 : r < 1) :
    (∫⁻ a in Iio (finiteParam r), omegaLower a ∂finiteMeasure nu) < ⊤ := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  let C : ℝ := r / (1 - r)
  have hbound : ∀ a ∈ Iio (finiteParam r),
      omegaLower a ≤ ENNReal.ofReal C := by
    intro a ha
    have haTop : a ≠ (⊤ : Param) := ne_top_of_lt (ha.trans_le le_top)
    let x : ℝ := ENNReal.toReal a
    have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
    have hxr : x < r := by
      dsimp only [x]
      exact ENNReal.toReal_lt_of_lt_ofReal ha
    have hx1 : x ≠ 1 := by linarith
    have hback : finiteParam x = a := by
      simpa only [x, paramToReal] using finiteParam_paramToReal a haTop
    have ha1 : a < (1 : Param) := by
      rw [← finiteParam_one]
      exact ha.trans (by
        change ENNReal.ofReal r < ENNReal.ofReal 1
        exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 hr1)
    rw [omegaLower, if_pos ⟨bot_le, ha1⟩, ← hback,
      singularWeight_finite hx0 hx1]
    apply ENNReal.ofReal_le_ofReal
    dsimp only [C]
    exact (div_le_div_iff₀ (by linarith : 0 < 1 - x)
      (by linarith : 0 < 1 - r)).mpr (by nlinarith)
  calc
    (∫⁻ a in Iio (finiteParam r), omegaLower a ∂finiteMeasure nu) ≤
        ∫⁻ _a in Iio (finiteParam r), ENNReal.ofReal C
          ∂finiteMeasure nu :=
      setLIntegral_mono measurable_const hbound
    _ = ENNReal.ofReal C *
        finiteMeasure nu (Iio (finiteParam r)) :=
      setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (measure_lt_top (finiteMeasure nu) _)

/-- The real lower truncation is the real value of the corresponding
extended nonnegative integral. -/
theorem lowerTrunc_eq_toReal_lowerLIntegral (nu : FiniteMeasure Param)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    lowerTrunc nu r = ENNReal.toReal
      (∫⁻ a in Iio (finiteParam r), omegaLower a ∂finiteMeasure nu) := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  have h := (signedWitnessIntegralBridge nu).2.2 r hr hr1
  calc
    lowerTrunc nu r =
        ∫ beta in Iio (finiteParam r), singularWeight beta
          ∂(nu : Measure Param) := rfl
    _ = lowerMoment (positiveSigned nu) r := by
      rw [lowerMoment, positiveSigned, signedIntegral_signedLift,
        integral_indicator measurableSet_Iio]
    _ = ENNReal.toReal
        (∫⁻ a in Iio (finiteParam r), omegaLower a
          ∂finiteMeasure nu) := h

/-- A real bound on a lower truncation gives the corresponding extended-real
bound once truncated finiteness has been established. -/
theorem lowerTruncatedLIntegral_le_of_lowerTrunc_le
    (nu : FiniteMeasure Param) {r C : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (_hC : 0 ≤ C)
    (hbound : lowerTrunc nu r ≤ C) :
    (∫⁻ a in Iio (finiteParam r), omegaLower a ∂finiteMeasure nu) ≤
      ENNReal.ofReal C := by
  let ell : ENNReal :=
    ∫⁻ a in Iio (finiteParam r), omegaLower a ∂finiteMeasure nu
  have hell : ell ≠ ⊤ := (lowerTruncatedLIntegral_lt_top nu hr hr1).ne
  change ell ≤ ENNReal.ofReal C
  rw [← ENNReal.ofReal_toReal hell]
  apply ENNReal.ofReal_le_ofReal
  have hreal := lowerTrunc_eq_toReal_lowerLIntegral nu hr hr1
  simpa only [ell] using hreal.symm.trans_le hbound

/-- A uniform extended-real bound on every null lower truncation passes to
the full lower singular moment. -/
theorem MLower_le_of_null_truncated_lintegrals
    (nu : FiniteMeasure Param) (C : ENNReal)
    (hbound : ∀ r : ℝ, 0 < r → r < 1 →
      finiteMeasure nu ({finiteParam r} : Set Param) = 0 →
      (∫⁻ a in Iio (finiteParam r), omegaLower a ∂finiteMeasure nu) ≤ C) :
    MLower (finiteMeasure nu) ≤ C := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  obtain ⟨r, hrmono, hr, hrtendsto⟩ :=
    exists_null_seq_below_one (finiteMeasure nu)
  let f : ℕ → Param → ENNReal := fun n a ↦
    (Iio (finiteParam (r n))).indicator omegaLower a
  have hfmeas : ∀ n, Measurable (f n) := by
    intro n
    exact measurable_omegaLower.indicator measurableSet_Iio
  have hfmono : ∀ a, Monotone (fun n ↦ f n a) := by
    intro a m n hmn
    change f m a ≤ f n a
    have hrle : r m ≤ r n := hrmono.monotone hmn
    have hparam : finiteParam (r m) ≤ finiteParam (r n) :=
      ENNReal.ofReal_le_ofReal hrle
    by_cases ham : a ∈ Iio (finiteParam (r m))
    · have han : a ∈ Iio (finiteParam (r n)) := lt_of_lt_of_le ham hparam
      simp only [f, Set.indicator_of_mem ham, Set.indicator_of_mem han]
      exact le_rfl
    · rw [show f m a = 0 by simp [f, ham]]
      exact bot_le
  have hftendsto : ∀ a,
      Tendsto (fun n ↦ f n a) atTop (𝓝 (omegaLower a)) := by
    intro a
    by_cases haIco : a ∈ Ico (0 : Param) 1
    · have haTop : a ≠ (⊤ : Param) := ne_top_of_lt haIco.2
      let x : ℝ := ENNReal.toReal a
      have hx1 : x < 1 := by
        dsimp only [x]
        exact (ENNReal.toReal_lt_toReal haTop ENNReal.one_ne_top).2 haIco.2
      have hback : finiteParam x = a := by
        simpa only [x, paramToReal] using finiteParam_paramToReal a haTop
      have hevent : ∀ᶠ n in atTop, x < r n :=
        hrtendsto.eventually (Ioi_mem_nhds hx1)
      apply tendsto_const_nhds.congr'
      filter_upwards [hevent] with n hn
      have hmem : a ∈ Iio (finiteParam (r n)) := by
        rw [← hback]
        change ENNReal.ofReal x < ENNReal.ofReal (r n)
        exact (ENNReal.ofReal_lt_ofReal_iff (hr n).1).2 hn
      exact (Set.indicator_of_mem hmem omegaLower).symm
    · have hzero : omegaLower a = 0 := by simp [omegaLower, haIco]
      have hfun : (fun n ↦ f n a) = fun _n : ℕ ↦ (0 : ENNReal) := by
        funext n
        simp [f, hzero]
      rw [hfun, hzero]
      exact tendsto_const_nhds
  have hlim := lintegral_tendsto_of_tendsto_of_monotone
    (μ := finiteMeasure nu)
    (fun n ↦ (hfmeas n).aemeasurable)
    (ae_of_all _ hfmono) (ae_of_all _ hftendsto)
  have hlim' : Tendsto
      (fun n ↦ ∫⁻ a in Iio (finiteParam (r n)), omegaLower a
        ∂finiteMeasure nu)
      atTop (𝓝 (MLower (finiteMeasure nu))) := by
    simpa only [f, lintegral_indicator measurableSet_Iio, MLower] using hlim
  apply le_of_tendsto' hlim'
  intro n
  exact hbound (r n) (hr n).1 (hr n).2.1 (hr n).2.2

/-- A uniform real inequality `1 ≤ A - lowerTrunc` at null thresholds gives
the full lower-moment bound by `A - 1`. -/
theorem MLower_le_of_truncated_difference
    (nu : FiniteMeasure Param) (A : ℝ) (hA : 0 ≤ A - 1)
    (hbound : ∀ r : ℝ, 0 < r → r < 1 →
      finiteMeasure nu ({finiteParam r} : Set Param) = 0 →
      1 ≤ A - lowerTrunc nu r) :
    MLower (finiteMeasure nu) ≤ ENNReal.ofReal (A - 1) := by
  apply MLower_le_of_null_truncated_lintegrals nu (ENNReal.ofReal (A - 1))
  intro r hr hr1 hnull
  apply lowerTruncatedLIntegral_le_of_lowerTrunc_le nu hr hr1 hA
  linarith [hbound r hr hr1 hnull]

end ConditionalEntropy
