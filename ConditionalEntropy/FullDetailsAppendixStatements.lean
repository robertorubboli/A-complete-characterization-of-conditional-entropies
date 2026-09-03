import BoundaryProofs.DominantBlock
import BoundaryProofs.Stationarity
import ConditionalEntropy.CurvatureObstructions
import ConditionalEntropy.Discretization
import ConditionalEntropy.EndpointParameterContinuity
import ConditionalEntropy.IntegratedEntropy
import ConditionalEntropy.MonomialCalculus
import ConditionalEntropy.PowerMean
import ConditionalEntropy.RenyiSchur
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Canonical declarations for Appendix A of the full-details paper

This module provides the main group of stable paper-facing declarations for
Appendix A.  The A.3/A.6 continuity-discretization pair and the larger A.11
signed-interchange theorem live in their own companion modules.  Together the
three Appendix modules provide one unique canonical name for every numbered
Appendix result.
-/

noncomputable section

open Filter MeasureTheory Set SignType
open scoped BigOperators ENNReal NNReal Topology ContDiff Interval

namespace ConditionalEntropy

universe u v

/-! ## A.1: power-mean Hessian -/

private def appendixPowerMeanLine {I : Type u} [Fintype I]
    (a : ℝ) (L : PositiveLineData I) (lambda : ℝ) : ℝ :=
  (linePowerSum L a lambda) ^ (1 / a)

private theorem hasDerivAt_appendixPowerMeanLine
    {I : Type u} [Fintype I] [Nonempty I]
    (a : ℝ) (ha : 0 < a) (L : PositiveLineData I)
    {lambda : ℝ} (h : LinePositive L lambda) :
    HasDerivAt (appendixPowerMeanLine a L)
      (appendixPowerMeanLine a L lambda * escortMean L a lambda) lambda := by
  have hP := hasDerivAt_linePowerSum (a := a) L h
  have hPpos := linePowerSum_pos L ha h
  have hr : HasDerivAt
      (fun s => (linePowerSum L a s) ^ (1 / a))
      ((a * lineWeightedFirst L a lambda) * (1 / a) *
        (linePowerSum L a lambda) ^ (1 / a - 1)) lambda :=
    hP.rpow_const (Or.inl hPpos.ne')
  apply hr.congr_deriv
  rw [escortMean_eq_lineWeightedFirst_div]
  unfold appendixPowerMeanLine
  rw [Real.rpow_sub_one hPpos.ne' (1 / a)]
  field_simp [ha.ne', hPpos.ne']

private theorem appendixPowerMeanLine_secondDerivative
    {I : Type u} [Fintype I] [Nonempty I]
    (a : ℝ) (ha : 0 < a) (L : PositiveLineData I)
    {lambda : ℝ} (h : LinePositive L lambda) :
    secondDeriv (appendixPowerMeanLine a L) lambda =
      (a - 1) * (linePowerSum L a lambda) ^ (1 / a - 2) *
        (linePowerSum L a lambda * lineWeightedSecond L a lambda -
          (lineWeightedFirst L a lambda) ^ 2) := by
  have hF := hasDerivAt_appendixPowerMeanLine a ha L h
  have hM := hasDerivAt_escortMean L ha h
  have hprod := hF.mul hM
  have hevent : deriv (appendixPowerMeanLine a L) =ᶠ[nhds lambda]
      fun s => appendixPowerMeanLine a L s * escortMean L a s := by
    filter_upwards [(isOpen_setOf_linePositive L).mem_nhds h] with s hs
    exact (hasDerivAt_appendixPowerMeanLine a ha L hs).deriv
  unfold secondDeriv
  rw [Filter.EventuallyEq.deriv_eq hevent]
  calc
    deriv (fun s => appendixPowerMeanLine a L s * escortMean L a s) lambda =
        appendixPowerMeanLine a L lambda * escortMean L a lambda *
            escortMean L a lambda +
          appendixPowerMeanLine a L lambda *
            ((a - 1) * escortSecond L a lambda -
              a * escortMean L a lambda ^ 2) := hprod.deriv
    _ = _ := by
      rw [escortMean_eq_lineWeightedFirst_div,
        escortSecond_eq_lineWeightedSecond_div]
      unfold appendixPowerMeanLine
      have hPpos := linePowerSum_pos L ha h
      rw [Real.rpow_sub hPpos (1 / a) 2]
      simp only [Real.rpow_two]
      field_simp [hPpos.ne']
      ring

private theorem appendixPowerMeanBracket_nonneg
    {I : Type u} [Fintype I] [Nonempty I]
    (a : ℝ) (_ha : 0 < a) (L : PositiveLineData I)
    {lambda : ℝ} (h : LinePositive L lambda) :
    0 ≤ linePowerSum L a lambda * lineWeightedSecond L a lambda -
      (lineWeightedFirst L a lambda) ^ 2 := by
  have hw0 : ∀ i, 0 ≤ lineRaw L lambda i ^ a := by
    intro i
    exact Real.rpow_nonneg (h i).le a
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i => lineRaw L lambda i ^ a * effectiveVelocity L lambda i)
    (f := fun i => lineRaw L lambda i ^ a)
    (g := fun i => lineRaw L lambda i ^ a *
      (effectiveVelocity L lambda i) ^ 2)
    (fun i _ => hw0 i)
    (fun i _ => mul_nonneg (hw0 i) (sq_nonneg _))
    (fun i _ => by
      rw [mul_pow]
      ring_nf
      exact le_rfl)
  apply sub_nonneg.mpr
  simpa only [linePowerSum, lineWeightedFirst, lineWeightedSecond] using hcs

/-- Appendix A.1: exact line-Hessian formula for the positive power mean,
nonnegativity of its Cauchy--Schwarz bracket, and the resulting cone-shape
classification including the top endpoint. -/
theorem fullDetailsAppendixA_1 {I : Type u} [Fintype I] [Nonempty I] :
    (∀ (a : ℝ), 0 < a → ∀ (L : PositiveLineData I) (lambda : ℝ),
      LinePositive L lambda →
        secondDeriv (appendixPowerMeanLine a L) lambda =
          (a - 1) * (linePowerSum L a lambda) ^ (1 / a - 2) *
            (linePowerSum L a lambda * lineWeightedSecond L a lambda -
              (lineWeightedFirst L a lambda) ^ 2)) ∧
    (∀ (a : ℝ), 0 < a → ∀ (L : PositiveLineData I) (lambda : ℝ),
      LinePositive L lambda →
        0 ≤ linePowerSum L a lambda * lineWeightedSecond L a lambda -
          (lineWeightedFirst L a lambda) ^ 2) ∧
    (∀ x : ConeVec I, lpNorm 1 x = l1Mass x.1) ∧
    ((∀ a : ℝ, 0 < a → a < 1 →
        ConcaveCone (fun x : ConeVec I => lpNorm a x)) ∧
      (∀ a : ℝ, 1 ≤ a →
        ConvexCone (fun x : ConeVec I => lpNorm a x)) ∧
      ConvexCone (fun x : ConeVec I => finMax x.1)) := by
  exact ⟨fun a ha L lambda h => appendixPowerMeanLine_secondDerivative a ha L h,
    fun a ha L lambda h => appendixPowerMeanBracket_nonneg a ha L h,
    fun x => by simp [lpNorm, l1Mass],
    powerCurvature⟩

/-! ## A.2: affine-monomial Hessian and sign classification -/

/-- Appendix A.2: the exact monomial line-Hessian identity and the iff
classifications of concavity and convexity. -/
theorem fullDetailsAppendixA_2
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (β : ι → ℝ) (hsum : IsAffineFamily β) :
    (∀ (L : PositiveLineData ι) (lambda : ℝ), LinePositive L lambda →
      secondDeriv (affineMonomialLine β L) lambda =
        affineMonomialLine β L lambda *
          monomialCurvature β (effectiveVelocity L lambda)) ∧
    (ConcaveOn ℝ (positiveOrthant : Set (ι → ℝ)) (affineMonomial β) ↔
      ∀ i, 0 ≤ β i) ∧
    (ConvexOn ℝ (positiveOrthant : Set (ι → ℝ)) (affineMonomial β) ↔
      HasUniquePositive β) := by
  exact ⟨fun L lambda h => affineMonomialLine_secondDerivative β L h,
    affineMonomial_concaveOn_iff β hsum,
    affineMonomial_convexOn_iff β hsum⟩

/-! ## A.4: Rényi shape properties -/

/-- Appendix A.4: all orders at most one are simplex-concave, while every
endpoint-aware order is Schur-concave under a doubly stochastic action. -/
theorem fullDetailsAppendixA_4
    {I : Type u} [Fintype I] [Nonempty I] :
    (∀ alpha : Param, alpha ≤ 1 → SimplexConcave (renyi alpha : ProbVec I → ℝ)) ∧
    (∀ (S : I → I → ℝ) (hS : DoublyStochastic S)
      (p : ProbVec I) (alpha : Param),
      renyi alpha p ≤ renyi alpha (probMatrixAction S hS p)) := by
  constructor
  · exact fun alpha halpha => renyiSimplexConcave alpha halpha
  · intro S hS p alpha
    exact renyiSchur S hS p alpha

/-! ## A.5: dominated convergence, monotone convergence, and Fubini -/

/-- Appendix A.5: the dominated-convergence, monotone-convergence, and
Fubini packages, with the standard measurability hypotheses made explicit. -/
theorem fullDetailsAppendixA_5
    {Ω Ω' E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : Measure Ω) (ρ : Measure Ω')
    [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    {fseq : ℕ → Ω → E} {f : Ω → E} {g : Ω → ℝ}
    (hfseq : ∀ n, AEStronglyMeasurable (fseq n) ν)
    (hg : Integrable g ν)
    (hdom : ∀ n : ℕ, Filter.Eventually
      (fun omega => ‖fseq n omega‖ ≤ g omega) (MeasureTheory.ae ν))
    (hlim : Filter.Eventually
      (fun omega => Tendsto (fun n => fseq n omega) atTop (nhds (f omega)))
      (MeasureTheory.ae ν))
    {useq : ℕ → Ω → ℝ≥0∞} {u : Ω → ℝ≥0∞}
    (huseq : ∀ n, AEMeasurable (useq n) ν)
    (humono : ∀ omega : Ω, Monotone fun n => useq n omega)
    (hulim : ∀ omega : Ω,
      Tendsto (fun n => useq n omega) atTop (nhds (u omega)))
    {F : Ω → Ω' → E}
    (hF : Integrable (Function.uncurry F) (ν.prod ρ)) :
    Tendsto (fun n => ∫ omega, fseq n omega ∂ν) atTop
        (nhds (∫ omega, f omega ∂ν)) ∧
      Tendsto (fun n => ∫⁻ omega, useq n omega ∂ν) atTop
        (nhds (∫⁻ omega, u omega ∂ν)) ∧
      Filter.Eventually (fun omega => Integrable (F omega) ρ) (MeasureTheory.ae ν) ∧
      Filter.Eventually (fun omega' => Integrable (fun omega => F omega omega') ν)
        (MeasureTheory.ae ρ) ∧
      (∫ omega, ∫ omega', F omega omega' ∂ρ ∂ν) =
        ∫ z, F z.1 z.2 ∂ν.prod ρ ∧
      (∫ omega', ∫ omega, F omega omega' ∂ν ∂ρ) =
        ∫ z, F z.1 z.2 ∂ν.prod ρ := by
  refine ⟨tendsto_integral_of_dominated_convergence g hfseq hg ?_ hlim,
    lintegral_tendsto_of_tendsto_of_monotone huseq ?_ ?_, hF.prod_right_ae,
    hF.prod_left_ae, integral_integral hF, ?_⟩
  · exact hdom
  · exact Filter.Eventually.of_forall humono
  · exact Filter.Eventually.of_forall hulim
  · exact (integral_prod_symm (Function.uncurry F) hF).symm

/-! ## A.7: pointwise closure of shape inequalities -/

/-- Appendix A.7: pointwise limits on a convex domain preserve concavity,
convexity, and quasi-convexity. -/
theorem fullDetailsAppendixA_7
    {E : Type u} [AddCommMonoid E] [Module ℝ E]
    (C : Set E) (hC : Convex ℝ C) (f : ℕ → E → ℝ) (g : E → ℝ)
    (hlim : ∀ x ∈ C, Tendsto (fun n => f n x) atTop (nhds (g x))) :
    ((∀ n, ConcaveOn ℝ C (f n)) → ConcaveOn ℝ C g) ∧
    ((∀ n, ConvexOn ℝ C (f n)) → ConvexOn ℝ C g) ∧
    ((∀ n, QuasiconvexOn ℝ C (f n)) → QuasiconvexOn ℝ C g) := by
  constructor
  · intro hf
    refine ⟨hC, ?_⟩
    intro x hx y hy a b ha hb hab
    have hleft : Tendsto (fun n => a * f n x + b * f n y) atTop
        (nhds (a * g x + b * g y)) :=
      (tendsto_const_nhds.mul (hlim x hx)).add
        (tendsto_const_nhds.mul (hlim y hy))
    refine le_of_tendsto_of_tendsto' hleft (hlim _ (hC hx hy ha hb hab)) ?_
    · intro n
      exact (hf n).2 hx hy ha hb hab
  constructor
  · intro hf
    refine ⟨hC, ?_⟩
    intro x hx y hy a b ha hb hab
    have hright : Tendsto (fun n => a * f n x + b * f n y) atTop
        (nhds (a * g x + b * g y)) :=
      (tendsto_const_nhds.mul (hlim x hx)).add
        (tendsto_const_nhds.mul (hlim y hy))
    refine le_of_tendsto_of_tendsto' (hlim _ (hC hx hy ha hb hab)) hright ?_
    · intro n
      exact (hf n).2 hx hy ha hb hab
  · intro hf
    rw [quasiconvexOn_iff_le_max]
    refine ⟨hC, ?_⟩
    intro x hx y hy a b ha hb hab
    have hmix := hC hx hy ha hb hab
    refine le_of_tendsto_of_tendsto' (hlim _ hmix) ((hlim x hx).max (hlim y hy)) ?_
    intro n
    exact (quasiconvexOn_iff_le_max.mp (hf n)).2 hx hy ha hb hab

/-! ## A.8: logarithmic power-mean derivatives -/

/-- The logarithmic power mean `ell_a(lambda)` used in Appendix A.8--A.9. -/
def appendixLogPowerMeanLine {I : Type u} [Fintype I]
    (a : ℝ) (L : PositiveLineData I) (lambda : ℝ) : ℝ :=
  (1 / a) * Real.log (linePowerSum L a lambda)

private theorem appendixLogPowerMeanLine_secondDerivative
    {I : Type u} [Fintype I] [Nonempty I]
    (a : ℝ) (ha : 0 < a) (L : PositiveLineData I)
    {lambda : ℝ} (h : LinePositive L lambda) :
    secondDeriv (appendixLogPowerMeanLine a L) lambda =
      -escortSecond L a lambda + a * escortVar L a lambda := by
  have hevent : deriv (appendixLogPowerMeanLine a L) =ᶠ[nhds lambda]
      escortMean L a := by
    filter_upwards [(isOpen_setOf_linePositive L).mem_nhds h] with s hs
    have hlog := (hasDerivAt_log_linePowerSum L ha hs).const_mul (1 / a)
    apply hlog.deriv.trans
    field_simp [ha.ne']
  have hmean := hasDerivAt_escortMean L ha h
  unfold secondDeriv
  rw [Filter.EventuallyEq.deriv_eq hevent]
  rw [hmean.deriv]
  unfold escortVar
  ring

/-- Appendix A.8: the first two logarithmic power-mean derivatives in escort
mean, second-moment, and variance form. -/
theorem fullDetailsAppendixA_8
    {I : Type u} [Fintype I] [Nonempty I]
    (a : ℝ) (ha : 0 < a) (L : PositiveLineData I)
    {lambda : ℝ} (h : LinePositive L lambda) :
    HasDerivAt (appendixLogPowerMeanLine a L)
      (escortMean L a lambda) lambda ∧
    HasDerivAt (escortMean L a)
      (-escortSecond L a lambda + a * escortVar L a lambda) lambda ∧
    secondDeriv (appendixLogPowerMeanLine a L) lambda =
      -escortSecond L a lambda + a * escortVar L a lambda ∧
    (-escortSecond L a lambda + a * escortVar L a lambda =
      (a - 1) * escortSecond L a lambda -
        a * (escortMean L a lambda) ^ 2) := by
  have hlog := (hasDerivAt_log_linePowerSum L ha h).const_mul (1 / a)
  have hfirst : HasDerivAt (appendixLogPowerMeanLine a L)
      (escortMean L a lambda) lambda := by
    apply hlog.congr_deriv
    field_simp [ha.ne']
  have hmean := hasDerivAt_escortMean L ha h
  have hsecond : HasDerivAt (escortMean L a)
      (-escortSecond L a lambda + a * escortVar L a lambda) lambda := by
    apply hmean.congr_deriv
    unfold escortVar
    ring
  exact ⟨hfirst, hsecond, appendixLogPowerMeanLine_secondDerivative a ha L h,
    by unfold escortVar; ring⟩

/-! ## A.9--A.10: Shannon cancellation and endpoint continuity -/

private def appendixLogPowerMeanAlpha {I : Type u} [Fintype I]
    (r : ℕ) (L : PositiveLineData I) (a lambda : ℝ) : ℝ :=
  match r with
  | 0 =>
      (-1 / a ^ 2) * Real.log (linePowerSum L a lambda) +
        (1 / a) * (lineLogPowerSum L a lambda / linePowerSum L a lambda)
  | 1 => escortMeanAlpha L a lambda
  | 2 =>
      -escortSecondAlpha L a lambda + escortVar L a lambda +
        a * escortVarAlpha L a lambda
  | _ => 0

private theorem continuousAt_lineLogPowerSum_pair
    {I : Type u} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) (a lambda : ℝ) (h : LinePositive L lambda) :
    ContinuousAt (fun p : ℝ × ℝ => lineLogPowerSum L p.1 p.2)
      (a, lambda) := by
  unfold lineLogPowerSum
  apply tendsto_finsetSum Finset.univ
  intro i _hi
  have hraw : ContinuousAt (fun p : ℝ × ℝ => lineRaw L p.2 i)
      (a, lambda) := by
    unfold lineRaw
    fun_prop
  exact (continuousAt_lineRaw_rpow_pair L i a lambda h).mul
    (hraw.log (h i).ne')

private theorem hasDerivAt_appendixLogPowerMean_order
    {I : Type u} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) {r : ℕ} (hr : r ≤ 2)
    {a lambda : ℝ} (ha : 0 < a) (h : LinePositive L lambda) :
    HasDerivAt
      (fun b => lambdaDeriv
        (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
        r b lambda)
      (alphaLambdaDeriv
        (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
        r a lambda) a := by
  apply DifferentiableAt.hasDerivAt
  interval_cases r
  · have hlog := (hasDerivAt_linePowerSum_order L a lambda h).log
      (linePowerSum_pos_all L a h).ne'
    have hquot := hlog.div (hasDerivAt_id a) ha.ne'
    have heq : (fun b => lambdaDeriv
        (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
        0 b lambda) =ᶠ[nhds a]
        (fun b => Real.log (linePowerSum L b lambda) / b) := by
      filter_upwards [] with b
      simp [lambdaDeriv, appendixLogPowerMeanLine, div_eq_mul_inv, mul_comm]
    exact hquot.differentiableAt.congr_of_eventuallyEq heq
  · have heq : (fun b => lambdaDeriv
        (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
        1 b lambda) =ᶠ[nhds a] (fun b => escortMean L b lambda) := by
      filter_upwards [Ioi_mem_nhds ha] with b hb
      simpa [lambdaDeriv, iteratedDeriv] using
        (fullDetailsAppendixA_8 b hb L h).1.deriv
    exact (hasDerivAt_escortMean_order L a lambda h).differentiableAt
      |>.congr_of_eventuallyEq heq
  · have heq : (fun b => lambdaDeriv
        (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
        2 b lambda) =ᶠ[nhds a]
        fun b => -escortSecond L b lambda + b * escortVar L b lambda := by
      filter_upwards [Ioi_mem_nhds ha] with b hb
      simpa [lambdaDeriv, iteratedDeriv, secondDeriv] using
        (fullDetailsAppendixA_8 b hb L h).2.2.1
    have hd := (hasDerivAt_escortSecond_order L a lambda h).neg.add
      ((hasDerivAt_id a).mul (hasDerivAt_escortVar_order L a lambda h))
    exact hd.differentiableAt.congr_of_eventuallyEq heq

private theorem continuousAt_appendixLogPowerMeanAlpha_pair
    {I : Type u} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) {r : ℕ} (hr : r ≤ 2)
    {a lambda : ℝ} (ha : 0 < a) (h : LinePositive L lambda) :
    ContinuousAt (fun p : ℝ × ℝ =>
      appendixLogPowerMeanAlpha r L p.1 p.2) (a, lambda) := by
  interval_cases r
  · have hP := continuousAt_linePowerSum_pair L a lambda h
    have hLP := continuousAt_lineLogPowerSum_pair L a lambda h
    have ha0 : (a : ℝ) ≠ 0 := ha.ne'
    have hInv : ContinuousAt (fun p : ℝ × ℝ => 1 / p.1) (a, lambda) :=
      continuousAt_const.div continuousAt_fst ha0
    have hInvSq : ContinuousAt (fun p : ℝ × ℝ => -1 / p.1 ^ 2)
        (a, lambda) :=
      continuousAt_const.div (continuousAt_fst.pow 2) (pow_ne_zero 2 ha0)
    change ContinuousAt
      (((fun p : ℝ × ℝ => -1 / p.1 ^ 2) *
          fun p => Real.log (linePowerSum L p.1 p.2)) +
        (fun p : ℝ × ℝ => 1 / p.1) *
          ((fun p => lineLogPowerSum L p.1 p.2) /
            fun p => linePowerSum L p.1 p.2)) (a, lambda)
    exact (hInvSq.mul (hP.log (linePowerSum_pos_all L a h).ne')).add
      (hInv.mul (hLP.div hP (linePowerSum_pos_all L a h).ne'))
  · simpa [appendixLogPowerMeanAlpha] using
      continuousAt_escortMeanAlpha_pair L a lambda h
  · change ContinuousAt
      (((-fun p : ℝ × ℝ => escortSecondAlpha L p.1 p.2) +
          fun p => escortVar L p.1 p.2) +
        Prod.fst * fun p => escortVarAlpha L p.1 p.2) (a, lambda)
    exact ((continuousAt_escortSecondAlpha_pair L a lambda h).neg.add
      (continuousAt_escortVar_pair L a lambda h)).add
        (continuousAt_fst.mul (continuousAt_escortVarAlpha_pair L a lambda h))

private theorem alphaLambdaDeriv_appendixLogPowerMeanLine
    {I : Type u} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) {r : ℕ} (hr : r ≤ 2)
    {a lambda : ℝ} (ha : 0 < a) (h : LinePositive L lambda) :
    alphaLambdaDeriv
        (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
        r a lambda = appendixLogPowerMeanAlpha r L a lambda := by
  interval_cases r
  · have hinv := (hasDerivAt_id a).inv ha.ne'
    have hlog := (hasDerivAt_linePowerSum_order L a lambda h).log
      (linePowerSum_pos_all L a h).ne'
    have heq : (fun b => lambdaDeriv
        (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
        0 b lambda) =ᶠ[nhds a]
        (id⁻¹ * fun b => Real.log (linePowerSum L b lambda)) := by
      filter_upwards [] with b
      simp [lambdaDeriv, appendixLogPowerMeanLine]
    unfold alphaLambdaDeriv
    rw [heq.deriv_eq, (hinv.mul hlog).deriv]
    simp [appendixLogPowerMeanAlpha]
  · have heq : (fun b => lambdaDeriv
        (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
        1 b lambda) =ᶠ[nhds a] (fun b => escortMean L b lambda) := by
      filter_upwards [Ioi_mem_nhds ha] with b hb
      simpa [lambdaDeriv, iteratedDeriv] using
        (fullDetailsAppendixA_8 b hb L h).1.deriv
    unfold alphaLambdaDeriv
    rw [heq.deriv_eq, (hasDerivAt_escortMean_order L a lambda h).deriv]
    rfl
  · have heq : (fun b => lambdaDeriv
        (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
        2 b lambda) =ᶠ[nhds a]
        fun b => -escortSecond L b lambda + b * escortVar L b lambda := by
      filter_upwards [Ioi_mem_nhds ha] with b hb
      simpa [lambdaDeriv, iteratedDeriv, secondDeriv] using
        (fullDetailsAppendixA_8 b hb L h).2.2.1
    have hd := (hasDerivAt_escortSecond_order L a lambda h).neg.add
      ((hasDerivAt_id a).mul (hasDerivAt_escortVar_order L a lambda h))
    have hop : (fun b => -escortSecond L b lambda + b * escortVar L b lambda) =ᶠ[
        nhds a] ((-fun b => escortSecond L b lambda) +
          id * fun b => escortVar L b lambda) := by
      filter_upwards [] with b
      simp
    unfold alphaLambdaDeriv
    rw [heq.deriv_eq, hop.deriv_eq, hd.deriv]
    simp [appendixLogPowerMeanAlpha]
    ring

private theorem appendixPoleCancellation
    (g : ℝ → ℝ) {a : ℝ} (ha : a ≠ 1)
    (hcont : ContinuousOn (fun b => deriv g b) (uIcc 1 a))
    (hderiv : ∀ b ∈ uIcc (1 : ℝ) a, HasDerivAt g (deriv g b) b) :
    a / (1 - a) * (g a - g 1) =
      -a * ∫ s in (0 : ℝ)..1, deriv g (1 + s * (a - 1)) := by
  have hFTC : (∫ b in (1 : ℝ)..a, deriv g b) = g a - g 1 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      hcont.intervalIntegrable
  have haffine : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => 1 + t * (a - 1)) (a - 1) s := by
    intro s _hs
    simpa only [id_eq, one_mul, mul_comm] using
      ((hasDerivAt_id s).const_mul (a - 1)).const_add 1
  have himage : (fun s : ℝ => 1 + s * (a - 1)) '' uIcc (0 : ℝ) 1 ⊆
      uIcc (1 : ℝ) a := by
    rintro _ ⟨s, hs, rfl⟩
    have hs' : s ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le zero_le_one] using hs
    exact (convex_uIcc (1 : ℝ) a).add_smul_sub_mem
      left_mem_uIcc right_mem_uIcc hs'
  have hchange := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := 1)
    (f := fun s : ℝ => 1 + s * (a - 1))
    (f' := fun _ => a - 1) (g := fun b => deriv g b)
    haffine continuous_const.continuousOn (hcont.mono himage)
  have hchange' : (∫ s in (0 : ℝ)..1,
      deriv g (1 + s * (a - 1)) * (a - 1)) =
      ∫ b in (1 : ℝ)..a, deriv g b := by
    simp only [Function.comp_apply, zero_mul, add_zero, one_mul] at hchange
    have hone : 1 + (a - 1) = a := by ring
    rw [hone] at hchange
    exact hchange
  have hfactor : (a - 1) *
      (∫ s in (0 : ℝ)..1, deriv g (1 + s * (a - 1))) = g a - g 1 := by
    rw [mul_comm, ← intervalIntegral.integral_mul_const]
    exact hchange'.trans hFTC
  rw [← hfactor]
  have hden : 1 - a ≠ 0 := sub_ne_zero.mpr ha.symm
  field_simp [hden]
  ring

private theorem appendixEntropyLineOrder_eq_weighted_logPowerMean
    {I : Type u} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) {r : ℕ} (hr : r ≤ 2)
    {a lambda : ℝ} (ha : 0 < a) (ha1 : a ≠ 1)
    (h : LinePositive L lambda) :
    lambdaDeriv
        (fun p : ℝ × ℝ => entropyLine L (finiteParam p.1) p.2)
        r a lambda =
      singularWeight (finiteParam a) *
        (lambdaDeriv
            (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
            r a lambda -
          lambdaDeriv
            (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
            r 1 lambda) := by
  interval_cases r
  · simp only [lambdaDeriv, iteratedDeriv]
    rw [entropyLine_finite_eq_formula L ha ha1 h,
      singularWeight_finite ha.le ha1]
    unfold finiteEntropyLineFormula appendixLogPowerMeanLine
    rw [linePowerSum_one]
    have hden : 1 - a ≠ 0 := sub_ne_zero.mpr ha1.symm
    field_simp [ha.ne', hden]
  · change entropyLineFirst L (finiteParam a) lambda = _
    rw [entropyLineFirst_finite_on L (isOpen_setOf_linePositive L)
      (fun _ hs => hs) ha ha1 h]
    have haDeriv := (fullDetailsAppendixA_8 a ha L h).1.deriv
    have hOneDeriv := (fullDetailsAppendixA_8 1 zero_lt_one L h).1.deriv
    congr 1
    rw [show lambdaDeriv
        (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
          1 a lambda = escortMean L a lambda by
          simpa [lambdaDeriv, iteratedDeriv] using haDeriv,
      show lambdaDeriv
        (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
          1 1 lambda = escortMean L 1 lambda by
          simpa [lambdaDeriv, iteratedDeriv] using hOneDeriv]
  · change entropyLineSecond L (finiteParam a) lambda = _
    rw [entropyLineSecond_finite_on L (isOpen_setOf_linePositive L)
      (fun _ hs => hs) ha ha1 h]
    have haSecond := (fullDetailsAppendixA_8 a ha L h).2.2.1
    have hOneSecond := (fullDetailsAppendixA_8 1 zero_lt_one L h).2.2.1
    rw [show lambdaDeriv
        (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
          2 a lambda =
            -escortSecond L a lambda + a * escortVar L a lambda by
          simpa [lambdaDeriv, iteratedDeriv, secondDeriv] using haSecond,
      show lambdaDeriv
        (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
          2 1 lambda =
            -escortSecond L 1 lambda + 1 * escortVar L 1 lambda by
          simpa [lambdaDeriv, iteratedDeriv, secondDeriv] using hOneSecond,
      singularWeight_finite ha.le ha1]
    unfold escortVar
    have hden : 1 - a ≠ 0 := sub_ne_zero.mpr ha1.symm
    field_simp [hden]
    ring

/-- Appendix A.9: the actual entropy and its first two line derivatives are
jointly continuous through the Shannon order.  At every positive finite order
different from one, the same three quantities satisfy the manuscript's exact
pole-cancellation formula for the logarithmic power mean. -/
theorem fullDetailsAppendixA_9
    {I : Type u} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) {lambda0 : ℝ}
    (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda) :
    (∀ lambda ∈ Icc (-lambda0) lambda0,
      ContinuousWithinAt (fun p : Param × ℝ => entropyLine L p.1 p.2)
          (Set.univ ×ˢ Icc (-lambda0) lambda0) (1, lambda) ∧
        ContinuousWithinAt (fun p : Param × ℝ => entropyLineFirst L p.1 p.2)
          (Set.univ ×ˢ Icc (-lambda0) lambda0) (1, lambda) ∧
        ContinuousWithinAt (fun p : Param × ℝ => entropyLineSecond L p.1 p.2)
          (Set.univ ×ˢ Icc (-lambda0) lambda0) (1, lambda)) ∧
    (∀ r : ℕ, r ≤ 2 → ∀ a : ℝ, 0 < a → a ≠ 1 →
      ∀ lambda ∈ Icc (-lambda0) lambda0,
        lambdaDeriv
            (fun p : ℝ × ℝ => entropyLine L (finiteParam p.1) p.2)
            r a lambda =
          singularWeight (finiteParam a) *
            (lambdaDeriv
                (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
                r a lambda -
              lambdaDeriv
                (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
                r 1 lambda) ∧
        singularWeight (finiteParam a) *
            (lambdaDeriv
                (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
                r a lambda -
              lambdaDeriv
                (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
                r 1 lambda) =
          -a * ∫ s in (0 : ℝ)..1,
            alphaLambdaDeriv
              (fun p : ℝ × ℝ => appendixLogPowerMeanLine p.1 L p.2)
              r (1 + s * (a - 1)) lambda) := by
  constructor
  · intro lambda hlambda
    exact continuousWithinAt_entropyLine_bundle_of_ne_top L hlambda0 hpos
      (a := (1 : Param)) (by simp) hlambda
  · intro r hr a ha ha1 lambda hlambda
    constructor
    · exact appendixEntropyLineOrder_eq_weighted_logPowerMean L hr ha ha1
        (hpos lambda hlambda)
    let F : ℝ × ℝ → ℝ :=
      fun p => appendixLogPowerMeanLine p.1 L p.2
    let g : ℝ → ℝ := fun b => lambdaDeriv F r b lambda
    have hline : LinePositive L lambda := hpos lambda hlambda
    have hpositive : ∀ b ∈ uIcc (1 : ℝ) a, 0 < b := by
      intro b hb
      rcases Set.mem_uIcc.mp hb with hb | hb
      · exact lt_of_lt_of_le zero_lt_one hb.1
      · exact lt_of_lt_of_le ha hb.1
    have hderiv : ∀ b ∈ uIcc (1 : ℝ) a,
        HasDerivAt g (deriv g b) b := by
      intro b hb
      have hd := hasDerivAt_appendixLogPowerMean_order L hr
        (hpositive b hb) hline
      exact hd.congr_deriv hd.deriv.symm
    have hexplicit : ContinuousOn
        (fun b => appendixLogPowerMeanAlpha r L b lambda) (uIcc 1 a) := by
      intro b hb
      exact ((continuousAt_appendixLogPowerMeanAlpha_pair L hr
        (hpositive b hb) hline).comp (x := b)
          (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
    have hcont : ContinuousOn (fun b => deriv g b) (uIcc 1 a) := by
      apply hexplicit.congr
      intro b hb
      have hactual := (hasDerivAt_appendixLogPowerMean_order L hr
        (hpositive b hb) hline).deriv
      have hexact := alphaLambdaDeriv_appendixLogPowerMeanLine L hr
        (hpositive b hb) hline
      simpa [g, F] using hactual.trans hexact
    rw [singularWeight_finite ha.le ha1]
    simpa [F, g, alphaLambdaDeriv] using
      appendixPoleCancellation g ha1 hcont hderiv

/-- Appendix A.10: the first two derivatives vanish and are jointly continuous
at order zero.  The second conjunct uses the manuscript's literal nonempty
maximizer set, positive `C²` profile, and uniform ratio gap; it supplies the
top-endpoint entropy formula and joint continuity of the first two derivatives. -/
theorem fullDetailsAppendixA_10
    {I : Type u} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) {lambda0 : ℝ}
    (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda) :
    (∀ lambda ∈ Icc (-lambda0) lambda0,
      entropyLineFirst L 0 lambda = 0 ∧
      entropyLineSecond L 0 lambda = 0 ∧
      ContinuousWithinAt (fun p : Param × ℝ => entropyLineFirst L p.1 p.2)
        (Set.univ ×ˢ Icc (-lambda0) lambda0) (0, lambda) ∧
      ContinuousWithinAt (fun p : Param × ℝ => entropyLineSecond L p.1 p.2)
        (Set.univ ×ˢ Icc (-lambda0) lambda0) (0, lambda)) ∧
    (∀ (J : Finset I), J.Nonempty → ∀ (m : ℝ → ℝ) (rho : ℝ),
      0 < rho → rho < 1 →
      (∀ lambda ∈ Icc (-lambda0) lambda0, 0 < m lambda) →
      ContDiffOn ℝ 2 m (Icc (-lambda0) lambda0) →
      (∀ lambda ∈ Icc (-lambda0) lambda0, ∀ i ∈ J,
        lineRaw L lambda i = m lambda) →
      (∀ lambda ∈ Icc (-lambda0) lambda0, ∀ i, i ∉ J →
        lineRaw L lambda i / m lambda ≤ rho) →
      (∀ lambda ∈ Icc (-lambda0) lambda0,
        entropyLine L ⊤ lambda =
          Real.log (lineMass L lambda) - Real.log (m lambda)) ∧
      ContinuousOn (fun p : Param × ℝ => entropyLine L p.1 p.2)
        (Set.univ ×ˢ Icc (-lambda0) lambda0) ∧
      ContinuousOn (fun p : Param × ℝ => entropyLineFirst L p.1 p.2)
        (Set.univ ×ˢ Icc (-lambda0) lambda0) ∧
      ContinuousOn (fun p : Param × ℝ => entropyLineSecond L p.1 p.2)
        (Set.univ ×ˢ Icc (-lambda0) lambda0)) := by
  constructor
  · intro lambda hlambda
    have hcont := continuousWithinAt_entropyLine_bundle_of_ne_top L hlambda0 hpos
      (a := (0 : Param)) (by simp) hlambda
    exact ⟨entropyLineFirst_zero L (hpos lambda hlambda),
      entropyLineSecond_zero L (hpos lambda hlambda), hcont.2.1, hcont.2.2⟩
  · intro J hJ m rho hrho0 hrho1 hmpos _hmSmooth hmax hgap
    obtain ⟨istar, histar⟩ := hJ
    have hzero : (0 : ℝ) ∈ Icc (-lambda0) lambda0 :=
      ⟨neg_nonpos.mpr hlambda0.le, hlambda0.le⟩
    have hright : lambda0 ∈ Icc (-lambda0) lambda0 :=
      ⟨by linarith, le_rfl⟩
    have hfixed : FixedMaxCoordinate L (Icc (-lambda0) lambda0) istar := by
      intro lambda hlambda
      refine ⟨hpos lambda hlambda, ?_, ?_⟩
      · intro i
        by_cases hi : i ∈ J
        · rw [hmax lambda hlambda i hi, hmax lambda hlambda istar histar]
        · have hle : lineRaw L lambda i ≤ rho * m lambda :=
            (div_le_iff₀ (hmpos lambda hlambda)).mp (hgap lambda hlambda i hi)
          calc
            lineRaw L lambda i ≤ rho * m lambda := hle
            _ ≤ m lambda :=
              mul_le_of_le_one_left (hmpos lambda hlambda).le hrho1.le
            _ = lineRaw L lambda istar :=
              (hmax lambda hlambda istar histar).symm
      · intro i heq
        have hi : i ∈ J := by
          by_contra hi
          have hle : lineRaw L lambda i ≤ rho * m lambda :=
            (div_le_iff₀ (hmpos lambda hlambda)).mp (hgap lambda hlambda i hi)
          have hlt : lineRaw L lambda i < lineRaw L lambda istar := by
            calc
              lineRaw L lambda i ≤ rho * m lambda := hle
              _ < m lambda := mul_lt_of_lt_one_left (hmpos lambda hlambda) hrho1
              _ = lineRaw L lambda istar :=
                (hmax lambda hlambda istar histar).symm
          exact (ne_of_lt hlt) heq
        have hx : L.x i = L.x istar := by
          have hi0 := hmax 0 hzero i hi
          have hk0 := hmax 0 hzero istar histar
          simpa [lineRaw] using hi0.trans hk0.symm
        have hline : lineRaw L lambda0 i = lineRaw L lambda0 istar :=
          (hmax lambda0 hright i hi).trans
            (hmax lambda0 hright istar histar).symm
        have hinner : 1 + L.u i * lambda0 = 1 + L.u istar * lambda0 := by
          rw [lineRaw, hx] at hline
          exact mul_left_cancel₀ (L.x_pos istar).ne' hline
        have huMul : L.u i * lambda0 = L.u istar * lambda0 := by linarith
        have hu : L.u i = L.u istar :=
          mul_right_cancel₀ hlambda0.ne' huMul
        simp [effectiveVelocity, hu]
    have hcont := continuousOn_entropyLine_full_bundle L hlambda0 hpos hfixed
    refine ⟨?_, hcont⟩
    intro lambda hlambda
    rw [← hmax lambda hlambda istar histar]
    exact entropyLine_top_of_max L (hpos lambda hlambda) istar
      (hfixed lambda hlambda).2.1

/-! ## A.12--A.15: dominant blocks, Shannon calculus, and stationarity -/

/-- Appendix A.12: the two dominant-block remainder estimates. -/
theorem fullDetailsAppendixA_12
    {ι : Type u} [Fintype ι]
    (π u : ι → ℝ) (j : ι) {α δ M : ℝ}
    (hπ : ∀ i, 0 ≤ π i) (hsum : ∑ i, π i = 1)
    (hdominant : 1 - δ ≤ π j) (hM : ∀ i, |u i| ≤ M)
    (hM0 : 0 ≤ M) (hα : 0 ≤ α) :
    |weightedMean π u - u j| ≤ 2 * M * δ ∧
    |(-weightedSecondMoment π u + α * weightedVariance π u) + u j ^ 2| ≤
      2 * M ^ 2 * (1 + 2 * α) * δ := by
  exact ⟨dominantBlock_first π u j hπ hsum hdominant hM hM0,
    dominantBlock_second π u j hπ hsum hdominant hM hα hM0⟩

/-- Appendix A.13: the exact first and second Shannon derivatives along a
strictly positive affine line.  `shannonLineSlope` is the negative covariance
in the paper, and `escortVar` is its variance. -/
theorem fullDetailsAppendixA_13
    {I : Type u} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) {lambda : ℝ} (h : LinePositive L lambda) :
    entropyLineFirst L 1 lambda = shannonLineSlope L lambda ∧
    entropyLineFirst L 1 lambda =
      -∑ i, (lineProb L lambda).1 i *
        (effectiveVelocity L lambda i - escortMean L 1 lambda) *
          Real.log ((lineProb L lambda).1 i) ∧
    entropyLineSecond L 1 lambda =
      -escortVar L 1 lambda -
        2 * escortMean L 1 lambda * shannonLineSlope L lambda := by
  refine ⟨entropyLineFirst_one L h, ?_, entropyLineSecond_one L h⟩
  simpa only [shannonLineSlope] using entropyLineFirst_one L h

/-- Appendix A.14: a stationary scalar curve that is twice differentiable
on a neighbourhood of zero and quasi-convex there has nonnegative second
derivative.  No continuity of the second derivative is assumed. -/
theorem fullDetailsAppendixA_14 {g : ℝ → ℝ} {eps : ℝ} (heps : 0 < eps)
    (htwice : ∀ x ∈ Ioo (-eps) eps,
      DifferentiableAt ℝ g x ∧ DifferentiableAt ℝ (deriv g) x)
    (hqcvx : ScalarQCvxOn (Ioo (-eps) eps) g)
    (hstationary : deriv g 0 = 0) :
    0 ≤ secondDeriv g 0 := by
  by_contra hnot
  have hsecond : secondDeriv g 0 < 0 := lt_of_not_ge hnot
  have hsignNhds :
      ∀ᶠ x in nhds (0 : ℝ), sign (deriv g x) = sign (0 - x) := by
    exact eventually_nhdsWithin_sign_eq_of_deriv_neg
      (f := deriv g) hsecond hstationary
  have hsignNE :
      ∀ᶠ x in 𝓝[≠] (0 : ℝ), sign (deriv g x) = sign (0 - x) :=
    hsignNhds.filter_mono nhdsWithin_le_nhds
  have hleftEventually : ∀ᶠ x in 𝓝[<] (0 : ℝ), 0 < deriv g x :=
    deriv_pos_left_of_sign_deriv hsignNE
  have hrightEventually : ∀ᶠ x in 𝓝[>] (0 : ℝ), deriv g x < 0 :=
    deriv_neg_right_of_sign_deriv hsignNE
  obtain ⟨a, ha0, ha⟩ := (nhdsLT_basis (0 : ℝ)).eventually_iff.mp hleftEventually
  obtain ⟨c, hc0, hc⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hrightEventually
  let m : ℝ := min (-a) (min c eps)
  have hm : 0 < m := lt_min (neg_pos.mpr ha0) (lt_min hc0 heps)
  let r : ℝ := m / 2
  have hr : 0 < r := div_pos hm (by norm_num)
  have hrm : r < m := by dsimp [r]; linarith
  have hra : r < -a := hrm.trans_le (min_le_left _ _)
  have hrc : r < c := hrm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hreps : r < eps :=
    hrm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hleftSubset : Icc (-r) 0 ⊆ Ioo (-eps) eps := by
    intro x hx
    exact ⟨(neg_lt_neg hreps).trans_le hx.1, hx.2.trans_lt heps⟩
  have hrightSubset : Icc 0 r ⊆ Ioo (-eps) eps := by
    intro x hx
    exact ⟨(neg_neg_of_pos heps).trans_le hx.1, hx.2.trans_lt hreps⟩
  have hleftDeriv : ∀ x ∈ interior (Icc (-r) 0), 0 < deriv g x := by
    intro x hx
    have hxIoo : x ∈ Ioo (-r) 0 := by
      simpa [interior_Icc, neg_lt_zero.mpr hr] using hx
    exact ha ⟨by linarith [hra, hxIoo.1], hxIoo.2⟩
  have hrightDeriv : ∀ x ∈ interior (Icc 0 r), deriv g x < 0 := by
    intro x hx
    have hxIoo : x ∈ Ioo 0 r := by
      simpa [interior_Icc, hr] using hx
    exact hc ⟨hxIoo.1, hxIoo.2.trans hrc⟩
  have hleftContinuous : ContinuousOn g (Icc (-r) 0) := by
    intro x hx
    exact (htwice x (hleftSubset hx)).1.continuousAt.continuousWithinAt
  have hrightContinuous : ContinuousOn g (Icc 0 r) := by
    intro x hx
    exact (htwice x (hrightSubset hx)).1.continuousAt.continuousWithinAt
  have hleftMono : StrictMonoOn g (Icc (-r) 0) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hleftContinuous hleftDeriv
  have hrightAnti : StrictAntiOn g (Icc 0 r) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _) hrightContinuous hrightDeriv
  have hleftValue : g (-r) < g 0 :=
    hleftMono ⟨le_rfl, neg_nonpos.mpr hr.le⟩
      ⟨neg_nonpos.mpr hr.le, le_rfl⟩ (neg_lt_zero.mpr hr)
  have hrightValue : g r < g 0 :=
    hrightAnti ⟨le_rfl, hr.le⟩ ⟨hr.le, le_rfl⟩ hr
  have hleftMem : -r ∈ Ioo (-eps) eps :=
    hleftSubset ⟨le_rfl, neg_nonpos.mpr hr.le⟩
  have hrightMem : r ∈ Ioo (-eps) eps :=
    hrightSubset ⟨hr.le, le_rfl⟩
  have hmix : (1 / 2 : ℝ) * (-r) + (1 - 1 / 2) * r = 0 := by ring
  have hmixMem :
      (1 / 2 : ℝ) * (-r) + (1 - 1 / 2) * r ∈ Ioo (-eps) eps := by
    rw [hmix]
    simpa using heps
  have hqc := hqcvx (-r) hleftMem r hrightMem (1 / 2)
    (by norm_num) (by norm_num) hmixMem
  rw [hmix] at hqc
  have hmax : max (g (-r)) (g r) < g 0 := max_lt hleftValue hrightValue
  linarith

/-- Appendix A.15: the manuscript's coordinate correction, eventual exact
stationarity, convergence of the corrected vectors, and passage of the
locally uniform second-order limit along those vectors. -/
theorem fullDetailsAppendixA_15
    {m : ℕ}
    (g : ℕ → (Fin m → ℝ) → ℝ → ℝ)
    (cN : ℕ → Fin m → ℝ) (cbar z : Fin m → ℝ) (Q : (Fin m → ℝ) → ℝ)
    (hfirst : ∀ n w, deriv (g n w) 0 = ∑ j, cN n j * w j)
    (hc : ∀ j, Tendsto (fun n => cN n j) atTop (nhds (cbar j)))
    (hQ : Continuous Q)
    (hsecond : ∀ K : Set (Fin m → ℝ), IsCompact K → K.Nonempty →
      TendstoUniformlyOn (fun n w => secondDeriv (g n w) 0) Q atTop K)
    (hstationary : ∑ j, cbar j * z j = 0)
    (k : Fin m) (hk : cbar k ≠ 0) :
    ∃ zN : ℕ → Fin m → ℝ,
      (∀ n j, zN n j =
        if j = k then z j - (∑ i, cN n i * z i) / cN n k else z j) ∧
      Tendsto zN atTop (nhds z) ∧
      (∀ᶠ n in atTop, cN n k ≠ 0 ∧ deriv (g n (zN n)) 0 = 0) ∧
      Tendsto (fun n => secondDeriv (g n (zN n)) 0) atTop (nhds (Q z)) := by
  let zN : ℕ → Fin m → ℝ := fun n j =>
    if j = k then z j - (∑ i, cN n i * z i) / cN n k else z j
  have hzN : Tendsto zN atTop (nhds z) := by
    simpa only [zN] using
      stationarityCorrection_tendsto cN cbar z k hc hstationary hk
  have hkN : ∀ᶠ n in atTop, cN n k ≠ 0 := (hc k).eventually_ne hk
  have hstationaryN : ∀ᶠ n in atTop, deriv (g n (zN n)) 0 = 0 := by
    filter_upwards [hkN] with n hn
    rw [hfirst]
    simpa only [zN] using stationarityCorrection_dot (cN n) z k hn
  let K : Set (Fin m → ℝ) := insert z (range zN)
  have hKcompact : IsCompact K := hzN.isCompact_insert_range
  have hKnonempty : K.Nonempty := ⟨z, mem_insert z (range zN)⟩
  have hzNmem : ∀ᶠ n in atTop, zN n ∈ K :=
    Filter.Eventually.of_forall fun n => mem_insert_iff.mpr (Or.inr ⟨n, rfl⟩)
  have hzNwithin : Tendsto zN atTop (nhdsWithin z K) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzN, hzNmem⟩
  have hsecondLimit :
      Tendsto (fun n => secondDeriv (g n (zN n)) 0) atTop (nhds (Q z)) :=
    (hsecond K hKcompact hKnonempty).tendsto_comp
      hQ.continuousWithinAt hzNwithin
  exact ⟨zN, fun n j => rfl, hzN, hkN.and hstationaryN, hsecondLimit⟩

end ConditionalEntropy
