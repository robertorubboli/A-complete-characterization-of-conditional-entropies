import ConditionalEntropy.LineCalculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Endpoint and parameter calculus for positive entropy lines

This module complements `LineCalculus` at orders zero, one, and infinity.
All line derivatives are proved only at points with coordinatewise strict
positivity.  Parameter-space claims use the total endpoint definitions, not
project-specific continuation axioms.
-/

noncomputable section

open Filter Set MeasureTheory intervalIntegral
open scoped BigOperators ENNReal NNReal Topology Interval

namespace ConditionalEntropy

universe u

/-! ## Generic iterated and mixed derivatives -/

/-- Iterated one-variable derivative, with zeroth derivative equal to the function. -/
def iteratedDeriv (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f
  | j + 1 => fun x => deriv (iteratedDeriv f j) x

@[simp] theorem iteratedDeriv_zero (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv f 0 x = f x := rfl

@[simp] theorem iteratedDeriv_succ (f : ℝ → ℝ) (j : ℕ) (x : ℝ) :
    iteratedDeriv f (j + 1) x = deriv (iteratedDeriv f j) x := rfl

/-- Iterated derivative in the second variable. -/
def lambdaDeriv (F : ℝ × ℝ → ℝ) (j : ℕ) (a lambda : ℝ) : ℝ :=
  iteratedDeriv (fun s => F (a, s)) j lambda

/-- Parameter derivative after iterated differentiation in the line variable. -/
def alphaLambdaDeriv (F : ℝ × ℝ → ℝ) (j : ℕ)
    (a lambda : ℝ) : ℝ :=
  deriv (fun b => lambdaDeriv F j b lambda) a

/-- Total removable quotient at the Shannon parameter. -/
def removableShannonQuotient (F : ℝ × ℝ → ℝ)
    (a lambda : ℝ) : ℝ :=
  if a = 1 then -alphaLambdaDeriv F 0 1 lambda else F (a, lambda) / (1 - a)

@[simp] theorem removableShannonQuotient_one (F : ℝ × ℝ → ℝ)
    (lambda : ℝ) :
    removableShannonQuotient F 1 lambda = -alphaLambdaDeriv F 0 1 lambda := by
  simp [removableShannonQuotient]

theorem removableShannonQuotient_of_ne (F : ℝ × ℝ → ℝ)
    {a lambda : ℝ} (ha : a ≠ 1) :
    removableShannonQuotient F a lambda = F (a, lambda) / (1 - a) := by
  simp [removableShannonQuotient, ha]

/-- Fundamental-theorem formula for the removable Shannon quotient.

This pointwise theorem isolates the analytic heart of the parameterized
removable-quotient argument.  Its hypotheses are exactly continuity of the
parameter derivative and the corresponding derivative identity along the
segment from `1` to `a`. -/
theorem removableShannonQuotient_eq_neg_integral (F : ℝ × ℝ → ℝ)
    {a lambda : ℝ} (hFone : F (1, lambda) = 0)
    (hcont : Continuous (fun b => alphaLambdaDeriv F 0 b lambda))
    (hderiv : ∀ b ∈ uIcc (1 : ℝ) a,
      HasDerivAt (fun r => F (r, lambda))
        (alphaLambdaDeriv F 0 b lambda) b) :
    removableShannonQuotient F a lambda =
      -∫ s in (0 : ℝ)..1,
        alphaLambdaDeriv F 0 (1 + s * (a - 1)) lambda := by
  by_cases ha : a = 1
  · subst a
    simp [removableShannonQuotient]
  · rw [removableShannonQuotient_of_ne F ha]
    have hFTC : (∫ b in (1 : ℝ)..a, alphaLambdaDeriv F 0 b lambda) =
        F (a, lambda) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        (hcont.intervalIntegrable 1 a), hFone, sub_zero]
    have haffine : ∀ s ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => 1 + t * (a - 1)) (a - 1) s := by
      intro s _hs
      simpa only [id_eq, one_mul, mul_comm] using
        ((hasDerivAt_id s).const_mul (a - 1)).const_add 1
    have hchange := intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := 1)
      (f := fun s : ℝ => 1 + s * (a - 1))
      (f' := fun _ => a - 1)
      (g := fun b => alphaLambdaDeriv F 0 b lambda)
      haffine continuous_const.continuousOn hcont
    have hchange' : (∫ s in (0 : ℝ)..1,
        alphaLambdaDeriv F 0 (1 + s * (a - 1)) lambda * (a - 1)) =
        ∫ b in (1 : ℝ)..a, alphaLambdaDeriv F 0 b lambda := by
      simp only [Function.comp_apply, zero_mul, add_zero, one_mul] at hchange
      have hone : 1 + (a - 1) = a := by ring
      rw [hone] at hchange
      exact hchange
    have hfactor : (a - 1) *
        (∫ s in (0 : ℝ)..1,
          alphaLambdaDeriv F 0 (1 + s * (a - 1)) lambda) = F (a, lambda) := by
      rw [mul_comm]
      rw [← intervalIntegral.integral_mul_const]
      exact hchange'.trans hFTC
    rw [← hfactor]
    have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
    field_simp [hden]
    ring

/-- Joint continuity of a removable quotient from a continuous mixed
derivative and a genuine parameter derivative everywhere.

The proof realizes the integral formula as the integral of a continuous-map
valued function on the compact interval `[0,1]`. -/
theorem continuousOn_removableShannonQuotient (F : ℝ × ℝ → ℝ)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (hFone : ∀ lambda, F (1, lambda) = 0)
    (hmixed : Continuous
      (fun p : ℝ × ℝ => alphaLambdaDeriv F 0 p.1 p.2))
    (hderiv : ∀ a lambda, HasDerivAt (fun b => F (b, lambda))
      (alphaLambdaDeriv F 0 a lambda) a) :
    ContinuousOn (fun p : ℝ × ℝ =>
      removableShannonQuotient F p.1 p.2) S := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let T := Set.Icc (0 : ℝ) 1
  letI : MeasureSpace T := Measure.Subtype.measureSpace
  letI : IsProbabilityMeasure (volume : Measure T) := {
    measure_univ := by
      dsimp only [T]
      rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc,
        Real.volume_Icc, sub_zero, ENNReal.ofReal_one] }
  let G : C(T × S, ℝ) :=
    ⟨fun z => alphaLambdaDeriv F 0
      (1 + z.1.1 * (z.2.1.1 - 1)) z.2.1.2, by
        have hc : Continuous (fun z : T × S =>
            ((1 + z.1.1 * (z.2.1.1 - 1), z.2.1.2) : ℝ × ℝ)) := by
          fun_prop
        exact hmixed.comp hc⟩
  have hGint : Integrable (G.curry : T → C(S, ℝ)) :=
    G.curry.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.intro isCompact_univ fun x hx =>
        (hx (Set.mem_univ x)).elim)
  let H : C(S, ℝ) := ∫ s : T, G.curry s
  have hHapply (p : S) : H p =
      ∫ s in (0 : ℝ)..1,
        alphaLambdaDeriv F 0 (1 + s * (p.1.1 - 1)) p.1.2 := by
    change (∫ s : T, G.curry s) p = _
    rw [ContinuousMap.integral_apply hGint p]
    change (∫ s : T,
      alphaLambdaDeriv F 0 (1 + s.1 * (p.1.1 - 1)) p.1.2) = _
    dsimp only [T]
    calc
      (∫ s : Set.Icc (0 : ℝ) 1,
          alphaLambdaDeriv F 0 (1 + s.1 * (p.1.1 - 1)) p.1.2) =
          ∫ s in Set.Icc (0 : ℝ) 1,
            alphaLambdaDeriv F 0 (1 + s * (p.1.1 - 1)) p.1.2 := by
        change (∫ s : Set.Icc (0 : ℝ) 1,
          alphaLambdaDeriv F 0 (1 + s.1 * (p.1.1 - 1)) p.1.2
            ∂Measure.comap Subtype.val volume) = _
        exact MeasureTheory.integral_subtype_comap (μ := volume)
          (show MeasurableSet (Set.Icc (0 : ℝ) 1) from measurableSet_Icc)
          (fun s : ℝ =>
            alphaLambdaDeriv F 0 (1 + s * (p.1.1 - 1)) p.1.2)
      _ = ∫ s in Set.Ioc (0 : ℝ) 1,
            alphaLambdaDeriv F 0 (1 + s * (p.1.1 - 1)) p.1.2 := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      _ = ∫ s in (0 : ℝ)..1,
            alphaLambdaDeriv F 0 (1 + s * (p.1.1 - 1)) p.1.2 := by
        rw [← intervalIntegral.integral_of_le zero_le_one]
  have hformula (p : S) :
      removableShannonQuotient F p.1.1 p.1.2 = -H p := by
    rw [hHapply]
    apply removableShannonQuotient_eq_neg_integral F (hFone p.1.2)
    · exact hmixed.comp <| continuous_id.prodMk continuous_const
    · intro b _hb
      exact hderiv b p.1.2
  rw [continuousOn_iff_continuous_restrict]
  have heq : S.restrict (fun p : ℝ × ℝ =>
      removableShannonQuotient F p.1 p.2) = fun p => -H p :=
    funext hformula
  rw [heq]
  exact H.continuous.neg

/-- A mixed-derivative form of the parameterized removable-quotient theorem.

The commutation hypothesis records that the first two line derivatives of
the quotient are the removable quotients of the corresponding line
derivatives.  Under that precise hypothesis, the theorem supplies both the
integral formula and joint continuity for orders `j ≤ 2`. -/
theorem parameterizedRemovableShannonQuotient_of_mixed
    (F : ℝ × ℝ → ℝ)
    {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (hzero : ∀ j : ℕ, j ≤ 2 → ∀ lambda, lambdaDeriv F j 1 lambda = 0)
    (hmixed : ∀ j : ℕ, j ≤ 2 → Continuous
      (fun p : ℝ × ℝ => alphaLambdaDeriv F j p.1 p.2))
    (hderiv : ∀ j : ℕ, j ≤ 2 → ∀ a lambda,
      HasDerivAt (fun b => lambdaDeriv F j b lambda)
        (alphaLambdaDeriv F j a lambda) a)
    (hcommute : ∀ j : ℕ, j ≤ 2 → ∀ a lambda,
      lambdaDeriv (fun p => removableShannonQuotient F p.1 p.2) j a lambda =
        removableShannonQuotient
          (fun p => lambdaDeriv F j p.1 p.2) a lambda) :
    ∀ j : ℕ, j ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ =>
        lambdaDeriv (fun q => removableShannonQuotient F q.1 q.2)
          j p.1 p.2) S ∧
      ∀ p : ℝ × ℝ,
        lambdaDeriv (fun q => removableShannonQuotient F q.1 q.2)
            j p.1 p.2 =
          -∫ s in (0 : ℝ)..1,
            alphaLambdaDeriv F j (1 + s * (p.1 - 1)) p.2 := by
  intro j hj
  let Fj : ℝ × ℝ → ℝ := fun p => lambdaDeriv F j p.1 p.2
  have hAlpha (a lambda : ℝ) :
      alphaLambdaDeriv Fj 0 a lambda = alphaLambdaDeriv F j a lambda := by
    rfl
  have hcontFj : ContinuousOn (fun p : ℝ × ℝ =>
      removableShannonQuotient Fj p.1 p.2) S := by
    apply continuousOn_removableShannonQuotient Fj hS
    · exact hzero j hj
    · simpa only [hAlpha] using hmixed j hj
    · intro a lambda
      simpa only [hAlpha] using hderiv j hj a lambda
  constructor
  · have heq : (fun p : ℝ × ℝ =>
        lambdaDeriv (fun q => removableShannonQuotient F q.1 q.2)
          j p.1 p.2) =
        fun p => removableShannonQuotient Fj p.1 p.2 := by
      funext p
      exact hcommute j hj p.1 p.2
    rw [heq]
    exact hcontFj
  · intro p
    rw [hcommute j hj]
    change removableShannonQuotient Fj p.1 p.2 = _
    rw [removableShannonQuotient_eq_neg_integral Fj (hzero j hj p.2)]
    · apply congrArg Neg.neg
      apply intervalIntegral.integral_congr
      intro s _hs
      change alphaLambdaDeriv Fj 0 (1 + s * (p.1 - 1)) p.2 = _
      exact hAlpha _ _
    · exact (hmixed j hj).comp <| continuous_id.prodMk continuous_const
    · intro b _hb
      simpa only [hAlpha] using hderiv j hj b p.2

/-! ## Positive normalized coordinates -/

section Endpoints

variable {I : Type u} [Fintype I] [Nonempty I]

/-- The centered logarithmic velocity of one normalized coordinate. -/
def centeredVelocity (L : PositiveLineData I) (lambda : ℝ) (i : I) : ℝ :=
  effectiveVelocity L lambda i - escortMean L 1 lambda

/-- A positive normalized line has full support. -/
theorem supportFinset_lineProb_of_positive (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) :
    supportFinset (lineProb L lambda).1 = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  simp only [supportFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [lineProb_apply_of_positive L h]
  exact (div_pos (h i) (lineMass_pos L h)).ne'

/-- Order-zero entropy is locally the logarithm of the ambient cardinality. -/
theorem entropyLine_zero_of_positive (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) :
    entropyLine L 0 lambda = Real.log (Fintype.card I : ℝ) := by
  rw [entropyLine, renyi_at_zero, renyiZero,
    supportFinset_lineProb_of_positive L h, Finset.card_univ]

/-- Order-zero entropy has zero derivative throughout the positive domain. -/
theorem hasDerivAt_entropyLine_zero (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) :
    HasDerivAt (entropyLine L 0) 0 lambda := by
  have heq : entropyLine L 0 =ᶠ[nhds lambda]
      fun _ => Real.log (Fintype.card I : ℝ) := by
    filter_upwards [(isOpen_setOf_linePositive L).mem_nhds h] with s hs
    exact entropyLine_zero_of_positive L hs
  exact (hasDerivAt_const lambda _).congr_of_eventuallyEq heq

/-- Exact first derivative at order zero. -/
theorem entropyLineFirst_zero (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) :
    entropyLineFirst L 0 lambda = 0 :=
  (hasDerivAt_entropyLine_zero L h).deriv

/-- The first derivative at order zero is locally constant. -/
theorem hasDerivAt_entropyLineFirst_zero (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) :
    HasDerivAt (entropyLineFirst L 0) 0 lambda := by
  have heq : entropyLineFirst L 0 =ᶠ[nhds lambda] fun _ => 0 := by
    filter_upwards [(isOpen_setOf_linePositive L).mem_nhds h] with s hs
    exact entropyLineFirst_zero L hs
  exact (hasDerivAt_const lambda 0).congr_of_eventuallyEq heq

/-- Exact second derivative at order zero. -/
theorem entropyLineSecond_zero (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) :
    entropyLineSecond L 0 lambda = 0 := by
  unfold entropyLineSecond secondDeriv
  change deriv (entropyLineFirst L 0) lambda = 0
  exact (hasDerivAt_entropyLineFirst_zero L h).deriv

omit [Nonempty I] in
/-- The mass derivative, written as the order-one escort numerator. -/
theorem hasDerivAt_lineMass_escort (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) :
    HasDerivAt (lineMass L) (lineWeightedFirst L 1 lambda) lambda := by
  have hp := hasDerivAt_linePowerSum (a := 1) L h
  simp only [one_mul] at hp
  convert hp using 1
  funext s
  exact (linePowerSum_one L s).symm

/-- Derivative of one normalized positive-line coordinate. -/
theorem hasDerivAt_lineProb_apply (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) (i : I) :
    HasDerivAt (fun s => (lineProb L s).1 i)
      ((lineProb L lambda).1 i * centeredVelocity L lambda i) lambda := by
  have hM := lineMass_pos L h
  have hquot : HasDerivAt (fun s => lineRaw L s i / lineMass L s)
      ((L.x i * L.u i * lineMass L lambda -
        lineRaw L lambda i * lineWeightedFirst L 1 lambda) /
        lineMass L lambda ^ 2) lambda := by
    exact (hasDerivAt_lineRaw L lambda i).div
      (hasDerivAt_lineMass_escort L h) hM.ne'
  have heq : (fun s => (lineProb L s).1 i) =ᶠ[nhds lambda]
      fun s => lineRaw L s i / lineMass L s := by
    filter_upwards [(isOpen_setOf_linePositive L).mem_nhds h] with s hs
    exact lineProb_apply_of_positive L hs i
  apply (hquot.congr_of_eventuallyEq heq).congr_deriv
  rw [lineProb_apply_of_positive L h, centeredVelocity,
    escortMean_eq_lineWeightedFirst_div,
    ← lineRaw_mul_effectiveVelocity L h i]
  rw [linePowerSum_one]
  field_simp [hM.ne']

/-- Positive normalized coordinates have the centered logarithmic derivative. -/
theorem hasDerivAt_log_lineProb_apply (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) (i : I) :
    HasDerivAt (fun s => Real.log ((lineProb L s).1 i))
      (centeredVelocity L lambda i) lambda := by
  have hpPos : 0 < (lineProb L lambda).1 i := by
    rw [lineProb_apply_of_positive L h]
    exact div_pos (h i) (lineMass_pos L h)
  have hd := (hasDerivAt_lineProb_apply L h i).log hpPos.ne'
  apply hd.congr_deriv
  field_simp [hpPos.ne']

/-- At order one, escort weights are the normalized line probabilities. -/
theorem escortWeight_one_eq_lineProb (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) (i : I) :
    escortWeight L 1 lambda i = (lineProb L lambda).1 i := by
  change lineRaw L lambda i ^ (1 : ℝ) / linePowerSum L 1 lambda = _
  rw [Real.rpow_one, linePowerSum_one,
    lineProb_apply_of_positive L h]

/-- Centered velocities have probability mean zero. -/
theorem sum_lineProb_mul_centeredVelocity_eq_zero (L : PositiveLineData I)
    {lambda : ℝ} (h : LinePositive L lambda) :
    ∑ i, (lineProb L lambda).1 i * centeredVelocity L lambda i = 0 := by
  have hmass : ∑ i, (lineProb L lambda).1 i = 1 := by
    simpa only [l1Mass] using (lineProb L lambda).2.2
  have hmean : ∑ i, (lineProb L lambda).1 i *
      effectiveVelocity L lambda i = escortMean L 1 lambda := by
    unfold escortMean
    apply Finset.sum_congr rfl
    intro i _hi
    rw [escortWeight_one_eq_lineProb L h i]
  simp only [centeredVelocity, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  rw [hmean, hmass, one_mul, sub_self]

/-- Escort variance at order one is the centered probability second moment. -/
theorem escortVar_one_eq_sum_centered_sq (L : PositiveLineData I)
    {lambda : ℝ} (h : LinePositive L lambda) :
    escortVar L 1 lambda =
      ∑ i, (lineProb L lambda).1 i * (centeredVelocity L lambda i) ^ 2 := by
  have hmass : ∑ i, (lineProb L lambda).1 i = 1 := by
    simpa only [l1Mass] using (lineProb L lambda).2.2
  have hmean : ∑ i, (lineProb L lambda).1 i *
      effectiveVelocity L lambda i = escortMean L 1 lambda := by
    unfold escortMean
    apply Finset.sum_congr rfl
    intro i _hi
    rw [escortWeight_one_eq_lineProb L h i]
  have hsecond : ∑ i, (lineProb L lambda).1 i *
      (effectiveVelocity L lambda i) ^ 2 = escortSecond L 1 lambda := by
    unfold escortSecond
    apply Finset.sum_congr rfl
    intro i _hi
    rw [escortWeight_one_eq_lineProb L h i]
  simp only [escortVar, centeredVelocity]
  symm
  calc
    ∑ i, (lineProb L lambda).1 i *
          (effectiveVelocity L lambda i - escortMean L 1 lambda) ^ 2 =
        ∑ i, ((lineProb L lambda).1 i *
            (effectiveVelocity L lambda i) ^ 2 -
          2 * escortMean L 1 lambda *
            ((lineProb L lambda).1 i * effectiveVelocity L lambda i) +
          (escortMean L 1 lambda) ^ 2 * (lineProb L lambda).1 i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = (∑ i, (lineProb L lambda).1 i *
            (effectiveVelocity L lambda i) ^ 2) -
          2 * escortMean L 1 lambda *
            (∑ i, (lineProb L lambda).1 i * effectiveVelocity L lambda i) +
          (escortMean L 1 lambda) ^ 2 *
            (∑ i, (lineProb L lambda).1 i) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [Finset.mul_sum, Finset.mul_sum]
    _ = escortSecond L 1 lambda - (escortMean L 1 lambda) ^ 2 := by
      rw [hsecond, hmean, hmass]
      ring

/-! ## Shannon endpoint -/

/-- Derivative of one Shannon summand along a positive line. -/
theorem hasDerivAt_shannonSummandLine (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) (i : I) :
    HasDerivAt
      (fun s => -((lineProb L s).1 i * Real.log ((lineProb L s).1 i)))
      (-((lineProb L lambda).1 i * centeredVelocity L lambda i *
        (Real.log ((lineProb L lambda).1 i) + 1))) lambda := by
  have hp := hasDerivAt_lineProb_apply L h i
  have hlog := hasDerivAt_log_lineProb_apply L h i
  have hprod := (hp.mul hlog).neg
  apply hprod.congr_deriv
  ring

/-- Shannon entropy has the manuscript's centered-velocity derivative. -/
theorem hasDerivAt_entropyLine_one (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) :
    HasDerivAt (entropyLine L 1) (shannonLineSlope L lambda) lambda := by
  have hs : HasDerivAt
      (fun s => ∑ i,
        -((lineProb L s).1 i * Real.log ((lineProb L s).1 i)))
      (∑ i, -((lineProb L lambda).1 i * centeredVelocity L lambda i *
        (Real.log ((lineProb L lambda).1 i) + 1))) lambda := by
    exact HasDerivAt.fun_sum fun i _ => hasDerivAt_shannonSummandLine L h i
  have heq : entropyLine L 1 =ᶠ[nhds lambda]
      fun s => ∑ i, -((lineProb L s).1 i * Real.log ((lineProb L s).1 i)) := by
    filter_upwards [] with s
    simp only [entropyLine, renyi_at_one, renyiOne, Finset.sum_neg_distrib]
  have hactual := hs.congr_of_eventuallyEq heq
  apply hactual.congr_deriv
  have hz := sum_lineProb_mul_centeredVelocity_eq_zero L h
  symm
  calc
    shannonLineSlope L lambda =
        ∑ i, -((lineProb L lambda).1 i * centeredVelocity L lambda i *
          Real.log ((lineProb L lambda).1 i)) := by
      simp only [shannonLineSlope, centeredVelocity, Finset.sum_neg_distrib]
    _ = ∑ i, (-((lineProb L lambda).1 i * centeredVelocity L lambda i *
          (Real.log ((lineProb L lambda).1 i) + 1)) +
        (lineProb L lambda).1 i * centeredVelocity L lambda i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = (∑ i, -((lineProb L lambda).1 i * centeredVelocity L lambda i *
          (Real.log ((lineProb L lambda).1 i) + 1))) +
        ∑ i, (lineProb L lambda).1 i * centeredVelocity L lambda i := by
      rw [Finset.sum_add_distrib]
    _ = ∑ i, -((lineProb L lambda).1 i * centeredVelocity L lambda i *
          (Real.log ((lineProb L lambda).1 i) + 1)) := by
      rw [hz, add_zero]

/-- Exact first derivative at the Shannon endpoint. -/
theorem entropyLineFirst_one (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) :
    entropyLineFirst L 1 lambda = shannonLineSlope L lambda :=
  (hasDerivAt_entropyLine_one L h).deriv

/-- Centered velocity derivative at a positive line point. -/
theorem hasDerivAt_centeredVelocity (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) (i : I) :
    HasDerivAt (fun s => centeredVelocity L s i)
      ((escortMean L 1 lambda) ^ 2 -
        (effectiveVelocity L lambda i) ^ 2) lambda := by
  have hm := hasDerivAt_escortMean L zero_lt_one h
  have hv := hasDerivAt_effectiveVelocity L h i
  have hsub : HasDerivAt
      ((fun s => effectiveVelocity L s i) - escortMean L 1)
      (-(effectiveVelocity L lambda i) ^ 2 -
        ((1 - 1) * escortSecond L 1 lambda -
          1 * (escortMean L 1 lambda) ^ 2)) lambda := by
    exact hv.sub hm
  have heq : (fun s => centeredVelocity L s i) =ᶠ[nhds lambda]
      (fun s => effectiveVelocity L s i) - escortMean L 1 := by
    filter_upwards [] with s
    rfl
  apply (hsub.congr_of_eventuallyEq heq).congr_deriv
  ring

/-- Derivative of one summand of the Shannon slope. -/
theorem hasDerivAt_shannonSlopeSummand (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) (i : I) :
    HasDerivAt
      (fun s => -((lineProb L s).1 i * centeredVelocity L s i *
        Real.log ((lineProb L s).1 i)))
      (2 * escortMean L 1 lambda *
          ((lineProb L lambda).1 i * centeredVelocity L lambda i *
            Real.log ((lineProb L lambda).1 i)) -
        (lineProb L lambda).1 i * (centeredVelocity L lambda i) ^ 2) lambda := by
  have hp := hasDerivAt_lineProb_apply L h i
  have hq := hasDerivAt_centeredVelocity L h i
  have hlog := hasDerivAt_log_lineProb_apply L h i
  have hprod := ((hp.mul hq).mul hlog).neg
  simp only [Pi.mul_apply] at hprod
  apply hprod.congr_deriv
  simp only [centeredVelocity]
  ring

/-- The Shannon slope has the exact second-derivative expression. -/
theorem hasDerivAt_shannonLineSlope (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) :
    HasDerivAt (shannonLineSlope L)
      (-escortVar L 1 lambda -
        2 * escortMean L 1 lambda * shannonLineSlope L lambda) lambda := by
  have hs : HasDerivAt
      (fun s => ∑ i, -((lineProb L s).1 i * centeredVelocity L s i *
        Real.log ((lineProb L s).1 i)))
      (∑ i, (2 * escortMean L 1 lambda *
          ((lineProb L lambda).1 i * centeredVelocity L lambda i *
            Real.log ((lineProb L lambda).1 i)) -
        (lineProb L lambda).1 i * (centeredVelocity L lambda i) ^ 2)) lambda := by
    exact HasDerivAt.fun_sum fun i _ => hasDerivAt_shannonSlopeSummand L h i
  have heq : shannonLineSlope L =ᶠ[nhds lambda]
      fun s => ∑ i, -((lineProb L s).1 i * centeredVelocity L s i *
        Real.log ((lineProb L s).1 i)) := by
    filter_upwards [] with s
    simp only [shannonLineSlope, centeredVelocity, Finset.sum_neg_distrib]
  apply (hs.congr_of_eventuallyEq heq).congr_deriv
  rw [escortVar_one_eq_sum_centered_sq L h]
  simp only [shannonLineSlope, centeredVelocity]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The entropy first derivative is differentiable at the Shannon endpoint. -/
theorem hasDerivAt_entropyLineFirst_one (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) :
    HasDerivAt (entropyLineFirst L 1)
      (-escortVar L 1 lambda -
        2 * escortMean L 1 lambda * shannonLineSlope L lambda) lambda := by
  have heq : entropyLineFirst L 1 =ᶠ[nhds lambda] shannonLineSlope L := by
    filter_upwards [(isOpen_setOf_linePositive L).mem_nhds h] with s hs
    exact entropyLineFirst_one L hs
  exact (hasDerivAt_shannonLineSlope L h).congr_of_eventuallyEq heq

/-- Exact second derivative at the Shannon endpoint. -/
theorem entropyLineSecond_one (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) :
    entropyLineSecond L 1 lambda =
      -escortVar L 1 lambda -
        2 * escortMean L 1 lambda * shannonLineSlope L lambda := by
  unfold entropyLineSecond secondDeriv
  change deriv (entropyLineFirst L 1) lambda = _
  exact (hasDerivAt_entropyLineFirst_one L h).deriv

/-! ## Min-entropy endpoint -/

/-- The chosen raw maximum remains the maximum after normalization. -/
theorem finMax_lineProb_eq_of_max (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) (istar : I)
    (hmax : ∀ i, lineRaw L lambda i ≤ lineRaw L lambda istar) :
    finMax (lineProb L lambda).1 = (lineProb L lambda).1 istar := by
  apply le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
    intro i _hi
    rw [lineProb_apply_of_positive L h, lineProb_apply_of_positive L h]
    exact (div_le_div_iff_of_pos_right (lineMass_pos L h)).2 (hmax i)
  · exact le_finMax (lineProb L lambda) istar

/-- Closed min-entropy formula when a coordinate is maximal. -/
theorem entropyLine_top_of_max (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) (istar : I)
    (hmax : ∀ i, lineRaw L lambda i ≤ lineRaw L lambda istar) :
    entropyLine L ⊤ lambda =
      Real.log (lineMass L lambda) - Real.log (lineRaw L lambda istar) := by
  rw [entropyLine, renyi_at_top, renyiTop,
    finMax_lineProb_eq_of_max L h istar hmax,
    lineProb_apply_of_positive L h,
    Real.log_div (h istar).ne' (lineMass_pos L h).ne']
  ring

/-- Logarithmic mass derivative in order-one escort notation. -/
theorem hasDerivAt_log_lineMass (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) :
    HasDerivAt (fun s => Real.log (lineMass L s))
      (escortMean L 1 lambda) lambda := by
  have hd := (hasDerivAt_lineMass_escort L h).log (lineMass_pos L h).ne'
  rw [escortMean_eq_lineWeightedFirst_div, linePowerSum_one]
  exact hd

omit [Fintype I] [Nonempty I] in
/-- Logarithmic derivative of a positive raw coordinate. -/
theorem hasDerivAt_log_lineRaw (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) (i : I) :
    HasDerivAt (fun s => Real.log (lineRaw L s i))
      (effectiveVelocity L lambda i) lambda := by
  have hd := (hasDerivAt_lineRaw L lambda i).log (h i).ne'
  apply hd.congr_deriv
  rw [← lineRaw_mul_effectiveVelocity L h i]
  field_simp [(h i).ne']

/-- Exact min-entropy derivative on an open fixed-max domain. -/
theorem hasDerivAt_entropyLine_top_on (L : PositiveLineData I)
    {U : Set ℝ} (hU : IsOpen U) {istar : I}
    (hfixed : FixedMaxCoordinate L U istar) {lambda : ℝ} (hlambda : lambda ∈ U) :
    HasDerivAt (entropyLine L ⊤)
      (escortMean L 1 lambda - effectiveVelocity L lambda istar) lambda := by
  have heq : entropyLine L ⊤ =ᶠ[nhds lambda]
      fun s => Real.log (lineMass L s) - Real.log (lineRaw L s istar) := by
    filter_upwards [hU.mem_nhds hlambda] with s hs
    exact entropyLine_top_of_max L (hfixed s hs).1 istar (hfixed s hs).2.1
  have hclosed := (hasDerivAt_log_lineMass L (hfixed lambda hlambda).1).sub
    (hasDerivAt_log_lineRaw L (hfixed lambda hlambda).1 istar)
  exact hclosed.congr_of_eventuallyEq heq

/-- Exact first derivative at min-entropy on an open fixed-max domain. -/
theorem entropyLineFirst_top_on (L : PositiveLineData I)
    {U : Set ℝ} (hU : IsOpen U) {istar : I}
    (hfixed : FixedMaxCoordinate L U istar) {lambda : ℝ} (hlambda : lambda ∈ U) :
    entropyLineFirst L ⊤ lambda =
      escortMean L 1 lambda - effectiveVelocity L lambda istar :=
  (hasDerivAt_entropyLine_top_on L hU hfixed hlambda).deriv

/-- The min-entropy first derivative is differentiable on a fixed-max domain. -/
theorem hasDerivAt_entropyLineFirst_top_on (L : PositiveLineData I)
    {U : Set ℝ} (hU : IsOpen U) {istar : I}
    (hfixed : FixedMaxCoordinate L U istar) {lambda : ℝ} (hlambda : lambda ∈ U) :
    HasDerivAt (entropyLineFirst L ⊤)
      ((effectiveVelocity L lambda istar) ^ 2 -
        (escortMean L 1 lambda) ^ 2) lambda := by
  have heq : entropyLineFirst L ⊤ =ᶠ[nhds lambda]
      fun s => escortMean L 1 s - effectiveVelocity L s istar := by
    filter_upwards [hU.mem_nhds hlambda] with s hs
    exact entropyLineFirst_top_on L hU hfixed hs
  have hmean := hasDerivAt_escortMean L zero_lt_one (hfixed lambda hlambda).1
  have hvel := hasDerivAt_effectiveVelocity L (hfixed lambda hlambda).1 istar
  have hclosed : HasDerivAt (escortMean L 1 -
      fun s => effectiveVelocity L s istar)
      (((1 - 1) * escortSecond L 1 lambda -
          1 * (escortMean L 1 lambda) ^ 2) -
        (-(effectiveVelocity L lambda istar) ^ 2)) lambda := by
    exact hmean.sub hvel
  have heqClosed : (fun s => escortMean L 1 s - effectiveVelocity L s istar) =ᶠ[nhds lambda]
      escortMean L 1 - fun s => effectiveVelocity L s istar := by
    filter_upwards [] with s
    rfl
  apply (hclosed.congr_of_eventuallyEq heqClosed).congr_of_eventuallyEq heq |>.congr_deriv
  ring

/-- Exact second derivative at min-entropy on an open fixed-max domain. -/
theorem entropyLineSecond_top_on (L : PositiveLineData I)
    {U : Set ℝ} (hU : IsOpen U) {istar : I}
    (hfixed : FixedMaxCoordinate L U istar) {lambda : ℝ} (hlambda : lambda ∈ U) :
    entropyLineSecond L ⊤ lambda =
      (effectiveVelocity L lambda istar) ^ 2 -
        (escortMean L 1 lambda) ^ 2 := by
  unfold entropyLineSecond secondDeriv
  change deriv (entropyLineFirst L ⊤) lambda = _
  exact (hasDerivAt_entropyLineFirst_top_on L hU hfixed hlambda).deriv

/-! ## Endpoint continuity in the line variable -/

/-- At order zero, the entropy and its first two line derivatives are
continuous throughout every positive line domain. -/
theorem continuousOn_entropyLine_zero_bundle (L : PositiveLineData I)
    {U : Set ℝ} (hpos : ∀ lambda ∈ U, LinePositive L lambda) :
    ContinuousOn (entropyLine L 0) U ∧
      ContinuousOn (entropyLineFirst L 0) U ∧
      ContinuousOn (entropyLineSecond L 0) U := by
  refine ⟨fun lambda hlambda =>
      (hasDerivAt_entropyLine_zero L (hpos lambda hlambda)).continuousAt.continuousWithinAt,
    fun lambda hlambda =>
      (hasDerivAt_entropyLineFirst_zero L (hpos lambda hlambda)).continuousAt.continuousWithinAt,
    ?_⟩
  intro lambda hlambda
  have heq : entropyLineSecond L 0 =ᶠ[nhdsWithin lambda U] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact entropyLineSecond_zero L (hpos s hs)
  exact continuousWithinAt_const.congr_of_eventuallyEq heq
    (entropyLineSecond_zero L (hpos lambda hlambda))

/-- At the Shannon order, the entropy and its first two line derivatives are
continuous throughout every positive line domain. -/
theorem continuousOn_entropyLine_one_bundle (L : PositiveLineData I)
    {U : Set ℝ} (hpos : ∀ lambda ∈ U, LinePositive L lambda) :
    ContinuousOn (entropyLine L 1) U ∧
      ContinuousOn (entropyLineFirst L 1) U ∧
      ContinuousOn (entropyLineSecond L 1) U := by
  refine ⟨fun lambda hlambda =>
      (hasDerivAt_entropyLine_one L (hpos lambda hlambda)).continuousAt.continuousWithinAt,
    fun lambda hlambda =>
      (hasDerivAt_entropyLineFirst_one L (hpos lambda hlambda)).continuousAt.continuousWithinAt,
    ?_⟩
  intro lambda hlambda
  have hp := hpos lambda hlambda
  have hvar : ContinuousAt (escortVar L 1) lambda :=
    (hasDerivAt_escortVar L zero_lt_one hp).continuousAt
  have hmean : ContinuousAt (escortMean L 1) lambda :=
    (hasDerivAt_escortMean L zero_lt_one hp).continuousAt
  have hslope : ContinuousAt (shannonLineSlope L) lambda :=
    (hasDerivAt_shannonLineSlope L hp).continuousAt
  have hclosed : ContinuousAt
      (fun s => -escortVar L 1 s -
        2 * escortMean L 1 s * shannonLineSlope L s) lambda := by
    fun_prop
  have heq : entropyLineSecond L 1 =ᶠ[nhdsWithin lambda U]
      fun s => -escortVar L 1 s -
        2 * escortMean L 1 s * shannonLineSlope L s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact entropyLineSecond_one L (hpos s hs)
  exact hclosed.continuousWithinAt.congr_of_eventuallyEq heq
    (entropyLineSecond_one L hp)

/-- On a fixed-max domain, min-entropy and its first two line derivatives are
continuous in the line parameter. -/
theorem continuousOn_entropyLine_top_bundle (L : PositiveLineData I)
    {U : Set ℝ} (hU : IsOpen U) {istar : I}
    (hfixed : FixedMaxCoordinate L U istar) :
    ContinuousOn (entropyLine L ⊤) U ∧
      ContinuousOn (entropyLineFirst L ⊤) U ∧
      ContinuousOn (entropyLineSecond L ⊤) U := by
  refine ⟨fun lambda hlambda =>
      (hasDerivAt_entropyLine_top_on L hU hfixed hlambda).continuousAt.continuousWithinAt,
    fun lambda hlambda =>
      (hasDerivAt_entropyLineFirst_top_on L hU hfixed hlambda).continuousAt.continuousWithinAt,
    ?_⟩
  intro lambda hlambda
  have hp := (hfixed lambda hlambda).1
  have hvel : ContinuousAt (fun s => effectiveVelocity L s istar) lambda :=
    (hasDerivAt_effectiveVelocity L hp istar).continuousAt
  have hmean : ContinuousAt (escortMean L 1) lambda :=
    (hasDerivAt_escortMean L zero_lt_one hp).continuousAt
  have hclosed : ContinuousAt
      (fun s => (effectiveVelocity L s istar) ^ 2 -
        (escortMean L 1 s) ^ 2) lambda := by
    fun_prop
  have heq : entropyLineSecond L ⊤ =ᶠ[nhdsWithin lambda U]
      fun s => (effectiveVelocity L s istar) ^ 2 -
        (escortMean L 1 s) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact entropyLineSecond_top_on L hU hfixed hs
  exact hclosed.continuousWithinAt.congr_of_eventuallyEq heq
    (entropyLineSecond_top_on L hU hfixed hlambda)

/-- All finite and endpoint derivative formulas on a symmetric positive interval.

This is the formula portion of the manuscript's `exactDerivatives` package;
the separate continuity package is intentionally not folded into this
statement. -/
theorem exactEntropyDerivativeFormulas (L : PositiveLineData I) {lambda0 : ℝ}
    (_hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda) :
    (∀ lambda ∈ Ioo (-lambda0) lambda0, ∀ a : ℝ,
      0 < a → a ≠ 1 →
        entropyLineFirst L (finiteParam a) lambda =
          singularWeight (finiteParam a) *
            (escortMean L a lambda - escortMean L 1 lambda) ∧
        entropyLineSecond L (finiteParam a) lambda =
          -a * escortVar L a lambda +
            singularWeight (finiteParam a) *
              ((escortMean L 1 lambda) ^ 2 -
                (escortMean L a lambda) ^ 2)) ∧
    (∀ lambda ∈ Ioo (-lambda0) lambda0,
      entropyLineFirst L 0 lambda = 0 ∧
      entropyLineSecond L 0 lambda = 0 ∧
      entropyLineFirst L 1 lambda = shannonLineSlope L lambda ∧
      entropyLineSecond L 1 lambda =
        -escortVar L 1 lambda -
          2 * escortMean L 1 lambda * shannonLineSlope L lambda) ∧
    (∀ istar : I, FixedMaxCoordinate L (Icc (-lambda0) lambda0) istar →
      ∀ lambda ∈ Ioo (-lambda0) lambda0,
        entropyLineFirst L ⊤ lambda =
          escortMean L 1 lambda - effectiveVelocity L lambda istar ∧
        entropyLineSecond L ⊤ lambda =
          (effectiveVelocity L lambda istar) ^ 2 -
            (escortMean L 1 lambda) ^ 2) := by
  have hOpen : IsOpen (Ioo (-lambda0) lambda0) := isOpen_Ioo
  have hOpenPos : ∀ lambda ∈ Ioo (-lambda0) lambda0,
      LinePositive L lambda := fun lambda hlambda =>
    hpos lambda (Ioo_subset_Icc_self hlambda)
  refine ⟨?_, ?_, ?_⟩
  · intro lambda hlambda a ha ha1
    exact ⟨entropyLineFirst_finite_on L hOpen hOpenPos ha ha1 hlambda,
      entropyLineSecond_finite_on L hOpen hOpenPos ha ha1 hlambda⟩
  · intro lambda hlambda
    have hp := hOpenPos lambda hlambda
    exact ⟨entropyLineFirst_zero L hp, entropyLineSecond_zero L hp,
      entropyLineFirst_one L hp, entropyLineSecond_one L hp⟩
  · intro istar hfixed lambda hlambda
    have hfixedOpen : FixedMaxCoordinate L (Ioo (-lambda0) lambda0) istar :=
      fun s hs => hfixed s (Ioo_subset_Icc_self hs)
    exact ⟨entropyLineFirst_top_on L hOpen hfixedOpen hlambda,
      entropyLineSecond_top_on L hOpen hfixedOpen hlambda⟩

end Endpoints

end ConditionalEntropy
