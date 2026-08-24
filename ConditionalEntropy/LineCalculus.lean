import ConditionalEntropy.LineData
import ConditionalEntropy.RenyiProperties

/-!
# Finite-order calculus on positive multiplicative lines

All derivative statements in this file are local to points where every line
coordinate is strictly positive.  The final lifting theorem assumes an open
set of such points, so the total fallback branch in `lineProb` is never used
near the differentiation point.
-/

noncomputable section

open Filter Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

section RawStatistics

variable {I : Type u} [Fintype I]

/-- Total mass of the raw positive line. -/
def lineMass (L : PositiveLineData I) (lambda : ℝ) : ℝ :=
  ∑ i, lineRaw L lambda i

/-- Raw power sum along a positive line. -/
def linePowerSum (L : PositiveLineData I) (a lambda : ℝ) : ℝ :=
  ∑ i, lineRaw L lambda i ^ a

/-- First escort numerator before division by the power sum. -/
def lineWeightedFirst (L : PositiveLineData I) (a lambda : ℝ) : ℝ :=
  ∑ i, lineRaw L lambda i ^ a * effectiveVelocity L lambda i

/-- Second escort numerator before division by the power sum. -/
def lineWeightedSecond (L : PositiveLineData I) (a lambda : ℝ) : ℝ :=
  ∑ i, lineRaw L lambda i ^ a * (effectiveVelocity L lambda i) ^ 2

/-- Third escort numerator before division by the power sum. -/
def lineWeightedThird (L : PositiveLineData I) (a lambda : ℝ) : ℝ :=
  ∑ i, lineRaw L lambda i ^ a * (effectiveVelocity L lambda i) ^ 3

/-- Escort third moment, used to state the variance derivative. -/
def escortThird (L : PositiveLineData I) (a lambda : ℝ) : ℝ :=
  ∑ i, escortWeight L a lambda i * (effectiveVelocity L lambda i) ^ 3

omit [Fintype I] in
/-- The raw line has its evident constant derivative. -/
theorem hasDerivAt_lineRaw (L : PositiveLineData I) (lambda : ℝ) (i : I) :
    HasDerivAt (fun s => lineRaw L s i) (L.x i * L.u i) lambda := by
  simpa [lineRaw, mul_add, mul_assoc] using
    ((hasDerivAt_const lambda (1 : ℝ)).add
      ((hasDerivAt_id lambda).const_mul (L.u i))).const_mul (L.x i)

/-- Positivity of the raw mass. -/
theorem lineMass_pos [Nonempty I] (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) : 0 < lineMass L lambda := by
  unfold lineMass
  exact Finset.sum_pos (fun i _ => h i) Finset.univ_nonempty

/-- Positivity of every positive-order raw power sum. -/
theorem linePowerSum_pos [Nonempty I] (L : PositiveLineData I) {a lambda : ℝ}
    (_ha : 0 < a) (h : LinePositive L lambda) : 0 < linePowerSum L a lambda := by
  unfold linePowerSum
  exact Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (h i) a)
    Finset.univ_nonempty

omit [Fintype I] in
/-- The affine derivative can be written as value times effective velocity. -/
theorem lineRaw_mul_effectiveVelocity (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) (i : I) :
    lineRaw L lambda i * effectiveVelocity L lambda i = L.x i * L.u i := by
  have hfactor : 0 < 1 + L.u i * lambda := by
    rcases (mul_pos_iff.mp (by simpa [lineRaw] using h i)) with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge (L.x_pos i).le hneg.1).elim
  simp only [lineRaw, effectiveVelocity]
  field_simp [hfactor.ne']

omit [Fintype I] in
/-- Effective velocity has derivative minus its square. -/
theorem hasDerivAt_effectiveVelocity (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) (i : I) :
    HasDerivAt (fun s => effectiveVelocity L s i)
      (-(effectiveVelocity L lambda i) ^ 2) lambda := by
  have hfactor : 1 + L.u i * lambda ≠ 0 := by
    intro hz
    have hx := h i
    simp [lineRaw, hz] at hx
  have hd : HasDerivAt (fun s : ℝ => 1 + L.u i * s) (L.u i) lambda := by
    simpa only [id_eq, mul_one, add_comm] using
      ((hasDerivAt_id lambda).const_mul (L.u i)).const_add 1
  have hq := (hasDerivAt_const lambda (L.u i)).div hd hfactor
  have hq' : HasDerivAt (fun s : ℝ => L.u i / (1 + L.u i * s))
      (-(L.u i / (1 + L.u i * lambda)) ^ 2) lambda := by
    apply hq.congr_deriv
    field_simp [hfactor]
    ring
  simpa only [effectiveVelocity] using hq'

omit [Fintype I] in
/-- Raw power has the escort-form derivative. -/
theorem hasDerivAt_lineRaw_rpow (L : PositiveLineData I) {a lambda : ℝ}
    (h : LinePositive L lambda) (i : I) :
    HasDerivAt (fun s => lineRaw L s i ^ a)
      (a * lineRaw L lambda i ^ a * effectiveVelocity L lambda i) lambda := by
  have hr : HasDerivAt (fun s => lineRaw L s i ^ a)
      (a * lineRaw L lambda i ^ (a - 1) * (L.x i * L.u i)) lambda := by
    convert (hasDerivAt_lineRaw L lambda i).rpow_const (Or.inl (h i).ne') using 1
    ring
  apply hr.congr_deriv
  rw [← lineRaw_mul_effectiveVelocity L h i]
  rw [Real.rpow_sub_one (h i).ne' a]
  field_simp [(h i).ne']

/-- The mass derivative is the sum of the coordinate slopes. -/
theorem hasDerivAt_lineMass (L : PositiveLineData I) (lambda : ℝ) :
    HasDerivAt (lineMass L) (∑ i, L.x i * L.u i) lambda := by
  unfold lineMass
  exact HasDerivAt.fun_sum fun i _ => hasDerivAt_lineRaw L lambda i

/-- The raw power-sum derivative. -/
theorem hasDerivAt_linePowerSum (L : PositiveLineData I) {a lambda : ℝ}
    (h : LinePositive L lambda) :
    HasDerivAt (linePowerSum L a)
      (a * lineWeightedFirst L a lambda) lambda := by
  have hs : HasDerivAt (fun s => ∑ i, lineRaw L s i ^ a)
      (∑ i, a * lineRaw L lambda i ^ a * effectiveVelocity L lambda i) lambda := by
    exact HasDerivAt.fun_sum fun i _ => hasDerivAt_lineRaw_rpow (a := a) L h i
  change HasDerivAt (fun s => ∑ i, lineRaw L s i ^ a)
    (a * ∑ i, lineRaw L lambda i ^ a * effectiveVelocity L lambda i) lambda
  apply hs.congr_deriv
  rw [Finset.mul_sum]
  simp only [mul_assoc]

/-- At order one, the raw power sum is the raw mass. -/
@[simp] theorem linePowerSum_one (L : PositiveLineData I) (lambda : ℝ) :
    linePowerSum L 1 lambda = lineMass L lambda := by
  simp [linePowerSum, lineMass]

/-- Escort means are quotients of their raw numerator and power sum. -/
theorem escortMean_eq_lineWeightedFirst_div (L : PositiveLineData I)
    (a lambda : ℝ) :
    escortMean L a lambda =
      lineWeightedFirst L a lambda / linePowerSum L a lambda := by
  simp only [escortMean, escortWeight, lineWeightedFirst, linePowerSum]
  rw [Finset.sum_div]
  congr 1
  funext i
  ring

/-- Escort second moments are quotients of their raw numerator and power sum. -/
theorem escortSecond_eq_lineWeightedSecond_div (L : PositiveLineData I)
    (a lambda : ℝ) :
    escortSecond L a lambda =
      lineWeightedSecond L a lambda / linePowerSum L a lambda := by
  simp only [escortSecond, escortWeight, lineWeightedSecond, linePowerSum]
  rw [Finset.sum_div]
  congr 1
  funext i
  ring

/-- Escort third moments are quotients of their raw numerator and power sum. -/
theorem escortThird_eq_lineWeightedThird_div (L : PositiveLineData I)
    (a lambda : ℝ) :
    escortThird L a lambda =
      lineWeightedThird L a lambda / linePowerSum L a lambda := by
  simp only [escortThird, escortWeight, lineWeightedThird, linePowerSum]
  rw [Finset.sum_div]
  congr 1
  funext i
  ring

/-- The first escort numerator has the expected second-moment derivative. -/
theorem hasDerivAt_lineWeightedFirst (L : PositiveLineData I) {a lambda : ℝ}
    (h : LinePositive L lambda) :
    HasDerivAt (lineWeightedFirst L a)
      ((a - 1) * lineWeightedSecond L a lambda) lambda := by
  have hs : HasDerivAt
      (fun s => ∑ i, lineRaw L s i ^ a * effectiveVelocity L s i)
      (∑ i, (a * lineRaw L lambda i ^ a * effectiveVelocity L lambda i *
          effectiveVelocity L lambda i +
        lineRaw L lambda i ^ a * (-(effectiveVelocity L lambda i) ^ 2))) lambda := by
    exact HasDerivAt.fun_sum fun i _ =>
      (hasDerivAt_lineRaw_rpow (a := a) L h i).mul
        (hasDerivAt_effectiveVelocity L h i)
  change HasDerivAt
    (fun s => ∑ i, lineRaw L s i ^ a * effectiveVelocity L s i)
    ((a - 1) * ∑ i,
      lineRaw L lambda i ^ a * (effectiveVelocity L lambda i) ^ 2) lambda
  apply hs.congr_deriv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The second escort numerator has the expected third-moment derivative. -/
theorem hasDerivAt_lineWeightedSecond (L : PositiveLineData I) {a lambda : ℝ}
    (h : LinePositive L lambda) :
    HasDerivAt (lineWeightedSecond L a)
      ((a - 2) * lineWeightedThird L a lambda) lambda := by
  have hs : HasDerivAt
      (fun s => ∑ i,
        lineRaw L s i ^ a * (effectiveVelocity L s i) ^ 2)
      (∑ i, (
        (a * lineRaw L lambda i ^ a * effectiveVelocity L lambda i) *
            (effectiveVelocity L lambda i) ^ 2 +
          lineRaw L lambda i ^ a *
            ((2 : ℝ) * (effectiveVelocity L lambda i) ^ (2 - 1) *
              (-(effectiveVelocity L lambda i) ^ 2)))) lambda := by
    exact HasDerivAt.fun_sum fun i _ =>
      (hasDerivAt_lineRaw_rpow (a := a) L h i).mul
        ((hasDerivAt_effectiveVelocity L h i).fun_pow 2)
  change HasDerivAt
    (fun s => ∑ i,
      lineRaw L s i ^ a * (effectiveVelocity L s i) ^ 2)
    ((a - 2) * ∑ i,
      lineRaw L lambda i ^ a * (effectiveVelocity L lambda i) ^ 3) lambda
  apply hs.congr_deriv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The logarithm of a positive raw power sum has escort derivative. -/
theorem hasDerivAt_log_linePowerSum [Nonempty I] (L : PositiveLineData I)
    {a lambda : ℝ} (ha : 0 < a) (h : LinePositive L lambda) :
    HasDerivAt (fun s => Real.log (linePowerSum L a s))
      (a * escortMean L a lambda) lambda := by
  have hp := (hasDerivAt_linePowerSum (a := a) L h).log
    (linePowerSum_pos L ha h).ne'
  rw [escortMean_eq_lineWeightedFirst_div]
  convert hp using 1
  ring

/-- The exact derivative of an escort mean on the positive line. -/
theorem hasDerivAt_escortMean [Nonempty I] (L : PositiveLineData I)
    {a lambda : ℝ} (ha : 0 < a) (h : LinePositive L lambda) :
    HasDerivAt (escortMean L a)
      ((a - 1) * escortSecond L a lambda -
        a * (escortMean L a lambda) ^ 2) lambda := by
  have hP := linePowerSum_pos L ha h
  have hquot : HasDerivAt
      (fun s => lineWeightedFirst L a s / linePowerSum L a s)
      (((a - 1) * lineWeightedSecond L a lambda * linePowerSum L a lambda -
        lineWeightedFirst L a lambda * (a * lineWeightedFirst L a lambda)) /
          linePowerSum L a lambda ^ 2) lambda := by
    exact (hasDerivAt_lineWeightedFirst (a := a) L h).div
      (hasDerivAt_linePowerSum (a := a) L h) hP.ne'
  have heq : escortMean L a =
      fun s => lineWeightedFirst L a s / linePowerSum L a s := by
    funext s
    exact escortMean_eq_lineWeightedFirst_div L a s
  rw [heq]
  apply hquot.congr_deriv
  rw [escortSecond_eq_lineWeightedSecond_div]
  field_simp [hP.ne']

/-- The exact derivative of an escort second moment. -/
theorem hasDerivAt_escortSecond [Nonempty I] (L : PositiveLineData I)
    {a lambda : ℝ} (ha : 0 < a) (h : LinePositive L lambda) :
    HasDerivAt (escortSecond L a)
      ((a - 2) * escortThird L a lambda -
        a * escortMean L a lambda * escortSecond L a lambda) lambda := by
  have hP := linePowerSum_pos L ha h
  have hquot : HasDerivAt
      (fun s => lineWeightedSecond L a s / linePowerSum L a s)
      (((a - 2) * lineWeightedThird L a lambda * linePowerSum L a lambda -
        lineWeightedSecond L a lambda *
          (a * lineWeightedFirst L a lambda)) /
        linePowerSum L a lambda ^ 2) lambda := by
    exact (hasDerivAt_lineWeightedSecond (a := a) L h).div
      (hasDerivAt_linePowerSum (a := a) L h) hP.ne'
  have heq : escortSecond L a =
      fun s => lineWeightedSecond L a s / linePowerSum L a s := by
    funext s
    exact escortSecond_eq_lineWeightedSecond_div L a s
  rw [heq]
  apply hquot.congr_deriv
  rw [escortThird_eq_lineWeightedThird_div,
    escortMean_eq_lineWeightedFirst_div]
  field_simp [hP.ne']

/-- The exact derivative of escort variance, expressed through its third moment. -/
theorem hasDerivAt_escortVar [Nonempty I] (L : PositiveLineData I)
    {a lambda : ℝ} (ha : 0 < a) (h : LinePositive L lambda) :
    HasDerivAt (escortVar L a)
      ((a - 2) * escortThird L a lambda -
        (3 * a - 2) * escortMean L a lambda * escortSecond L a lambda +
        2 * a * (escortMean L a lambda) ^ 3) lambda := by
  have hsecond := hasDerivAt_escortSecond L ha h
  have hmean := hasDerivAt_escortMean L ha h
  have hraw : HasDerivAt
      (escortSecond L a - escortMean L a * escortMean L a)
      (((a - 2) * escortThird L a lambda -
          a * escortMean L a lambda * escortSecond L a lambda) -
        (((a - 1) * escortSecond L a lambda -
            a * (escortMean L a lambda) ^ 2) * escortMean L a lambda +
          escortMean L a lambda *
            ((a - 1) * escortSecond L a lambda -
              a * (escortMean L a lambda) ^ 2))) lambda := by
    exact hsecond.sub (hmean.mul hmean)
  have heq : escortVar L a =ᶠ[nhds lambda]
      escortSecond L a - escortMean L a * escortMean L a := by
    filter_upwards [] with s
    simp only [escortVar, Pi.sub_apply, Pi.mul_apply]
    ring
  apply (hraw.congr_of_eventuallyEq heq).congr_deriv
  ring

/-- Algebraic escort-variance form of the escort-mean derivative. -/
theorem escortMean_derivative_eq_variance (L : PositiveLineData I)
    (a lambda : ℝ) :
    (a - 1) * escortSecond L a lambda -
        a * (escortMean L a lambda) ^ 2 =
      (a - 1) * escortVar L a lambda -
        (escortMean L a lambda) ^ 2 := by
  simp only [escortVar]
  ring

end RawStatistics

section FiniteEntropyFormula

variable {I : Type u} [Fintype I] [Nonempty I]

/-- On the positive branch, normalization is raw mass division coordinatewise. -/
theorem lineProb_apply_of_positive (L : PositiveLineData I) {lambda : ℝ}
    (h : LinePositive L lambda) (i : I) :
    (lineProb L lambda).1 i = lineRaw L lambda i / lineMass L lambda := by
  rw [lineProb_of_positive L lambda h, normalize_apply]
  rfl

/-- Power sums of a normalized positive line are homogeneous quotients. -/
theorem powerSum_lineProb_of_positive (L : PositiveLineData I) (a : ℝ)
    {lambda : ℝ} (h : LinePositive L lambda) :
    powerSum a (lineProb L lambda) =
      linePowerSum L a lambda / lineMass L lambda ^ a := by
  have hM := lineMass_pos L h
  unfold powerSum linePowerSum
  simp_rw [lineProb_apply_of_positive L h]
  simp_rw [Real.div_rpow (h _).le hM.le a]
  rw [Finset.sum_div]

/-- Closed finite-order entropy formula in raw positive-line coordinates. -/
def finiteEntropyLineFormula (L : PositiveLineData I) (a lambda : ℝ) : ℝ :=
  (Real.log (linePowerSum L a lambda) -
    a * Real.log (lineMass L lambda)) / (1 - a)

/-- The endpoint-aware definition reduces locally to the closed finite formula. -/
theorem entropyLine_finite_eq_formula (L : PositiveLineData I) {a lambda : ℝ}
    (ha : 0 < a) (ha1 : a ≠ 1) (h : LinePositive L lambda) :
    entropyLine L (finiteParam a) lambda = finiteEntropyLineFormula L a lambda := by
  rw [entropyLine, renyi_finite ha.le ha.ne' ha1]
  unfold renyiFinite finiteEntropyLineFormula
  rw [powerSum_lineProb_of_positive L a h]
  have hP := linePowerSum_pos L ha h
  have hM := lineMass_pos L h
  rw [Real.log_div hP.ne' (Real.rpow_pos_of_pos hM a).ne', Real.log_rpow hM]

/-- The first derivative of the closed finite-order formula. -/
theorem hasDerivAt_finiteEntropyLineFormula (L : PositiveLineData I)
    {a lambda : ℝ} (ha : 0 < a) (ha1 : a ≠ 1)
    (h : LinePositive L lambda) :
    HasDerivAt (finiteEntropyLineFormula L a)
      (a / (1 - a) *
        (escortMean L a lambda - escortMean L 1 lambda)) lambda := by
  have haOne : (0 : ℝ) < 1 := zero_lt_one
  have hlogA := hasDerivAt_log_linePowerSum L ha h
  have hlogOne := hasDerivAt_log_linePowerSum L haOne h
  have hlogMass : HasDerivAt (fun s => Real.log (lineMass L s))
      (escortMean L 1 lambda) lambda := by
    simpa only [linePowerSum_one, one_mul] using hlogOne
  have hnum : HasDerivAt
      ((fun s => Real.log (linePowerSum L a s)) -
        fun s => a * Real.log (lineMass L s))
      (a * escortMean L a lambda - a * escortMean L 1 lambda) lambda := by
    exact hlogA.sub (hlogMass.const_mul a)
  have hscaled : HasDerivAt
      (fun s => (1 - a)⁻¹ *
        (((fun t => Real.log (linePowerSum L a t)) -
          fun t => a * Real.log (lineMass L t)) s))
      ((1 - a)⁻¹ *
        (a * escortMean L a lambda - a * escortMean L 1 lambda)) lambda := by
    exact hnum.const_mul (1 - a)⁻¹
  have heq : finiteEntropyLineFormula L a =ᶠ[nhds lambda]
      fun s => (1 - a)⁻¹ *
        (((fun t => Real.log (linePowerSum L a t)) -
          fun t => a * Real.log (lineMass L t)) s) := by
    filter_upwards [] with s
    simp only [finiteEntropyLineFormula, Pi.sub_apply]
    ring
  have hdiv := hscaled.congr_of_eventuallyEq heq
  have hden : 1 - a ≠ 0 := sub_ne_zero.mpr ha1.symm
  apply hdiv.congr_deriv
  field_simp [hden]

/-- The derivative of the closed first-derivative expression. -/
theorem hasDerivAt_finiteEntropyLineFirstFormula (L : PositiveLineData I)
    {a lambda : ℝ} (ha : 0 < a) (ha1 : a ≠ 1)
    (h : LinePositive L lambda) :
    HasDerivAt
      (fun s => a / (1 - a) * (escortMean L a s - escortMean L 1 s))
      (-a * escortVar L a lambda +
        a / (1 - a) *
          ((escortMean L 1 lambda) ^ 2 - (escortMean L a lambda) ^ 2)) lambda := by
  have hmeanA := hasDerivAt_escortMean L ha h
  have hmeanOne := hasDerivAt_escortMean L zero_lt_one h
  have hsub : HasDerivAt
      (escortMean L a - escortMean L 1)
      (((a - 1) * escortSecond L a lambda -
          a * (escortMean L a lambda) ^ 2) -
        ((1 - 1) * escortSecond L 1 lambda -
          1 * (escortMean L 1 lambda) ^ 2)) lambda := by
    exact hmeanA.sub hmeanOne
  have hderiv : HasDerivAt
      (fun s => a / (1 - a) * ((escortMean L a - escortMean L 1) s))
      (a / (1 - a) *
        (((a - 1) * escortSecond L a lambda -
            a * (escortMean L a lambda) ^ 2) -
          ((1 - 1) * escortSecond L 1 lambda -
            1 * (escortMean L 1 lambda) ^ 2))) lambda := by
    exact hsub.const_mul (a / (1 - a))
  have hden : 1 - a ≠ 0 := sub_ne_zero.mpr ha1.symm
  have heq : (fun s => a / (1 - a) *
      (escortMean L a s - escortMean L 1 s)) =ᶠ[nhds lambda]
      fun s => a / (1 - a) * ((escortMean L a - escortMean L 1) s) := by
    filter_upwards [] with s
    rfl
  apply (hderiv.congr_of_eventuallyEq heq).congr_deriv
  simp only [escortVar]
  field_simp [hden]
  ring

end FiniteEntropyFormula

section PositiveOpenCalculus

variable {I : Type u} [Fintype I] [Nonempty I]

/-- Exact first derivative of finite-order Renyi entropy on a positive open set. -/
theorem hasDerivAt_entropyLine_finite_on (L : PositiveLineData I)
    {U : Set ℝ} (hU : IsOpen U) (hUpos : ∀ s ∈ U, LinePositive L s)
    {a lambda : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) (hlambda : lambda ∈ U) :
    HasDerivAt (entropyLine L (finiteParam a))
      (singularWeight (finiteParam a) *
        (escortMean L a lambda - escortMean L 1 lambda)) lambda := by
  have heq : entropyLine L (finiteParam a) =ᶠ[nhds lambda]
      finiteEntropyLineFormula L a := by
    filter_upwards [hU.mem_nhds hlambda] with s hs
    exact entropyLine_finite_eq_formula L ha ha1 (hUpos s hs)
  have hformula := hasDerivAt_finiteEntropyLineFormula L ha ha1
    (hUpos lambda hlambda)
  rw [singularWeight_finite ha.le ha1]
  exact hformula.congr_of_eventuallyEq heq

/-- Exact finite-order first-derivative identity on a positive open set. -/
theorem entropyLineFirst_finite_on (L : PositiveLineData I)
    {U : Set ℝ} (hU : IsOpen U) (hUpos : ∀ s ∈ U, LinePositive L s)
    {a lambda : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) (hlambda : lambda ∈ U) :
    entropyLineFirst L (finiteParam a) lambda =
      singularWeight (finiteParam a) *
        (escortMean L a lambda - escortMean L 1 lambda) := by
  exact (hasDerivAt_entropyLine_finite_on L hU hUpos ha ha1 hlambda).deriv

/-- The entropy-line first derivative is itself differentiable on a positive open set. -/
theorem hasDerivAt_entropyLineFirst_finite_on (L : PositiveLineData I)
    {U : Set ℝ} (hU : IsOpen U) (hUpos : ∀ s ∈ U, LinePositive L s)
    {a lambda : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) (hlambda : lambda ∈ U) :
    HasDerivAt (entropyLineFirst L (finiteParam a))
      (-a * escortVar L a lambda +
        singularWeight (finiteParam a) *
          ((escortMean L 1 lambda) ^ 2 -
            (escortMean L a lambda) ^ 2)) lambda := by
  have heq : entropyLineFirst L (finiteParam a) =ᶠ[nhds lambda]
      fun s => a / (1 - a) *
        (escortMean L a s - escortMean L 1 s) := by
    filter_upwards [hU.mem_nhds hlambda] with s hs
    rw [entropyLineFirst_finite_on L hU hUpos ha ha1 hs,
      singularWeight_finite ha.le ha1]
  have hformula := hasDerivAt_finiteEntropyLineFirstFormula L ha ha1
    (hUpos lambda hlambda)
  rw [singularWeight_finite ha.le ha1]
  exact hformula.congr_of_eventuallyEq heq

/-- Exact finite-order second-derivative identity on a positive open set. -/
theorem entropyLineSecond_finite_on (L : PositiveLineData I)
    {U : Set ℝ} (hU : IsOpen U) (hUpos : ∀ s ∈ U, LinePositive L s)
    {a lambda : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) (hlambda : lambda ∈ U) :
    entropyLineSecond L (finiteParam a) lambda =
      -a * escortVar L a lambda +
        singularWeight (finiteParam a) *
          ((escortMean L 1 lambda) ^ 2 -
            (escortMean L a lambda) ^ 2) := by
  unfold entropyLineSecond secondDeriv
  change deriv (entropyLineFirst L (finiteParam a)) lambda = _
  exact (hasDerivAt_entropyLineFirst_finite_on L hU hUpos ha ha1 hlambda).deriv

omit [Fintype I] [Nonempty I] in
/-- The coordinatewise-positive parameter set is open for finite line data. -/
theorem isOpen_setOf_linePositive [Finite I] (L : PositiveLineData I) :
    IsOpen {s : ℝ | LinePositive L s} := by
  rw [show {s : ℝ | LinePositive L s} =
      ⋂ i, {s : ℝ | 0 < lineRaw L s i} by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_iInter, LinePositive]]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_lt continuous_const
  unfold lineRaw
  fun_prop

/-- First-derivative specialization at the positive base point. -/
theorem entropyLineFirst_finite_zero (L : PositiveLineData I)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) :
    entropyLineFirst L (finiteParam a) 0 =
      singularWeight (finiteParam a) *
        (escortMean L a 0 - escortMean L 1 0) := by
  exact entropyLineFirst_finite_on L (isOpen_setOf_linePositive L)
    (fun s hs => hs) ha ha1 (linePositiveZero L)

/-- Second-derivative specialization at the positive base point. -/
theorem entropyLineSecond_finite_zero (L : PositiveLineData I)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) :
    entropyLineSecond L (finiteParam a) 0 =
      -a * escortVar L a 0 +
        singularWeight (finiteParam a) *
          ((escortMean L 1 0) ^ 2 - (escortMean L a 0) ^ 2) := by
  exact entropyLineSecond_finite_on L (isOpen_setOf_linePositive L)
    (fun s hs => hs) ha ha1 (linePositiveZero L)

/-- Expanded manuscript algebra for the second derivative at the base point. -/
theorem entropyLineSecond_finite_zero_expanded (L : PositiveLineData I)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) :
    entropyLineSecond L (finiteParam a) 0 =
      (a * (a - 1) * escortSecond L a 0 -
          a ^ 2 * (escortMean L a 0) ^ 2 +
        a * (escortMean L 1 0) ^ 2) / (1 - a) := by
  rw [entropyLineSecond_finite_zero L ha ha1,
    singularWeight_finite ha.le ha1]
  simp only [escortVar]
  have hden : 1 - a ≠ 0 := sub_ne_zero.mpr ha1.symm
  field_simp [hden]
  ring

end PositiveOpenCalculus

end ConditionalEntropy
