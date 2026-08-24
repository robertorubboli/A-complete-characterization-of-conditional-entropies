import ConditionalEntropy.EndpointLineCalculus
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Order.WithTop

/-!
# Joint endpoint continuity for entropy lines

This module supplies the continuity component of the exact-derivative
package.  Its auxiliary results are local: positivity gives smooth finite
escort statistics, while a fixed maximal coordinate gives exponential
escort concentration at the compactified upper endpoint.
-/

noncomputable section

open Filter Set MeasureTheory intervalIntegral
open scoped BigOperators ENNReal NNReal Topology Interval

namespace ConditionalEntropy

universe u

section LocalFiniteParameter

variable {I : Type u} [Fintype I] [Nonempty I]

/-- Every real-order raw power sum is positive at a positive line point. -/
theorem linePowerSum_pos_all (L : PositiveLineData I) (a : ℝ) {lambda : ℝ}
    (h : LinePositive L lambda) :
    0 < linePowerSum L a lambda := by
  unfold linePowerSum
  exact Finset.sum_pos (fun i _ => Real.rpow_pos_of_pos (h i) a)
    Finset.univ_nonempty

omit [Fintype I] [Nonempty I] in
/-- Joint continuity of one raw real power in order and line parameter. -/
theorem continuousAt_lineRaw_rpow_pair (L : PositiveLineData I)
    (i : I) (a lambda : ℝ) (h : LinePositive L lambda) :
    ContinuousAt (fun p : ℝ × ℝ => lineRaw L p.2 i ^ p.1) (a, lambda) := by
  have hraw : ContinuousAt (fun p : ℝ × ℝ => lineRaw L p.2 i) (a, lambda) := by
    unfold lineRaw
    fun_prop
  exact hraw.rpow continuousAt_fst (Or.inl (h i).ne')

omit [Nonempty I] in
/-- Joint continuity of the raw power sum. -/
theorem continuousAt_linePowerSum_pair (L : PositiveLineData I)
    (a lambda : ℝ) (h : LinePositive L lambda) :
    ContinuousAt (fun p : ℝ × ℝ => linePowerSum L p.1 p.2) (a, lambda) := by
  unfold linePowerSum
  exact tendsto_finsetSum Finset.univ fun i _hi =>
    (continuousAt_lineRaw_rpow_pair L i a lambda h)

omit [Fintype I] [Nonempty I] in
/-- Joint continuity of an effective velocity at a positive line point. -/
theorem continuousAt_effectiveVelocity_pair (L : PositiveLineData I)
    (i : I) (a lambda : ℝ) (h : LinePositive L lambda) :
    ContinuousAt (fun p : ℝ × ℝ => effectiveVelocity L p.2 i) (a, lambda) := by
  unfold effectiveVelocity
  apply ContinuousAt.div continuousAt_const
  · fun_prop
  · intro hzero
    have hx := h i
    simp [lineRaw, hzero] at hx

/-- Joint continuity of one escort weight. -/
theorem continuousAt_escortWeight_pair (L : PositiveLineData I)
    (i : I) (a lambda : ℝ) (h : LinePositive L lambda) :
    ContinuousAt (fun p : ℝ × ℝ => escortWeight L p.1 p.2 i)
      (a, lambda) := by
  unfold escortWeight
  exact (continuousAt_lineRaw_rpow_pair L i a lambda h).div
    (continuousAt_linePowerSum_pair L a lambda h)
    (linePowerSum_pos_all L a h).ne'

/-- Escort means are jointly continuous in finite order and line parameter. -/
theorem continuousAt_escortMean_pair (L : PositiveLineData I)
    (a lambda : ℝ) (h : LinePositive L lambda) :
    ContinuousAt (fun p : ℝ × ℝ => escortMean L p.1 p.2)
      (a, lambda) := by
  unfold escortMean
  exact tendsto_finsetSum Finset.univ fun i _hi =>
    (continuousAt_escortWeight_pair L i a lambda h).mul
      (continuousAt_effectiveVelocity_pair L i a lambda h)

/-- Escort second moments are jointly continuous in finite order and line parameter. -/
theorem continuousAt_escortSecond_pair (L : PositiveLineData I)
    (a lambda : ℝ) (h : LinePositive L lambda) :
    ContinuousAt (fun p : ℝ × ℝ => escortSecond L p.1 p.2)
      (a, lambda) := by
  unfold escortSecond
  exact tendsto_finsetSum Finset.univ fun i _hi =>
    (continuousAt_escortWeight_pair L i a lambda h).mul
      ((continuousAt_effectiveVelocity_pair L i a lambda h).pow 2)

/-- Escort variances are jointly continuous in finite order and line parameter. -/
theorem continuousAt_escortVar_pair (L : PositiveLineData I)
    (a lambda : ℝ) (h : LinePositive L lambda) :
    ContinuousAt (fun p : ℝ × ℝ => escortVar L p.1 p.2)
      (a, lambda) := by
  unfold escortVar
  exact (continuousAt_escortSecond_pair L a lambda h).sub
    ((continuousAt_escortMean_pair L a lambda h).pow 2)

/-- The closed finite entropy formula is jointly continuous away from order one. -/
theorem continuousAt_finiteEntropyLineFormula_pair (L : PositiveLineData I)
    (a lambda : ℝ) (ha : a ≠ 1) (h : LinePositive L lambda) :
    ContinuousAt (fun p : ℝ × ℝ => finiteEntropyLineFormula L p.1 p.2)
      (a, lambda) := by
  unfold finiteEntropyLineFormula
  have hpow := continuousAt_linePowerSum_pair L a lambda h
  have hmass : ContinuousAt (fun p : ℝ × ℝ => lineMass L p.2) (a, lambda) := by
    unfold lineMass lineRaw
    fun_prop
  apply ContinuousAt.div
  · exact (hpow.log (linePowerSum_pos_all L a h).ne').sub
      (continuousAt_fst.mul (hmass.log (lineMass_pos L h).ne'))
  · fun_prop
  · exact sub_ne_zero.mpr ha.symm

/-! ### Derivatives in the finite order parameter -/

/-- Logarithmic derivative numerator of the raw power sum. -/
def lineLogPowerSum (L : PositiveLineData I) (a lambda : ℝ) : ℝ :=
  ∑ i, lineRaw L lambda i ^ a * Real.log (lineRaw L lambda i)

/-- Logarithmic order derivative of the first escort numerator. -/
def lineLogWeightedFirst (L : PositiveLineData I) (a lambda : ℝ) : ℝ :=
  ∑ i, lineRaw L lambda i ^ a * Real.log (lineRaw L lambda i) *
    effectiveVelocity L lambda i

/-- Logarithmic order derivative of the second escort numerator. -/
def lineLogWeightedSecond (L : PositiveLineData I) (a lambda : ℝ) : ℝ :=
  ∑ i, lineRaw L lambda i ^ a * Real.log (lineRaw L lambda i) *
    (effectiveVelocity L lambda i) ^ 2

/-- Explicit order derivative of the escort mean. -/
def escortMeanAlpha (L : PositiveLineData I) (a lambda : ℝ) : ℝ :=
  lineLogWeightedFirst L a lambda / linePowerSum L a lambda -
    escortMean L a lambda *
      (lineLogPowerSum L a lambda / linePowerSum L a lambda)

/-- Explicit order derivative of the escort second moment. -/
def escortSecondAlpha (L : PositiveLineData I) (a lambda : ℝ) : ℝ :=
  lineLogWeightedSecond L a lambda / linePowerSum L a lambda -
    escortSecond L a lambda *
      (lineLogPowerSum L a lambda / linePowerSum L a lambda)

/-- Explicit order derivative of the escort variance. -/
def escortVarAlpha (L : PositiveLineData I) (a lambda : ℝ) : ℝ :=
  escortSecondAlpha L a lambda -
    2 * escortMean L a lambda * escortMeanAlpha L a lambda

omit [Nonempty I] in
/-- The raw power sum has the expected order derivative. -/
theorem hasDerivAt_linePowerSum_order (L : PositiveLineData I)
    (a lambda : ℝ) (h : LinePositive L lambda) :
    HasDerivAt (fun b => linePowerSum L b lambda)
      (lineLogPowerSum L a lambda) a := by
  unfold linePowerSum lineLogPowerSum
  apply HasDerivAt.fun_sum
  intro i _hi
  simpa only [mul_comm] using
    (Real.hasStrictDerivAt_const_rpow (h i) a).hasDerivAt

omit [Nonempty I] in
/-- The first raw escort numerator has the expected order derivative. -/
theorem hasDerivAt_lineWeightedFirst_order (L : PositiveLineData I)
    (a lambda : ℝ) (h : LinePositive L lambda) :
    HasDerivAt (fun b => lineWeightedFirst L b lambda)
      (lineLogWeightedFirst L a lambda) a := by
  unfold lineWeightedFirst lineLogWeightedFirst
  apply HasDerivAt.fun_sum
  intro i _hi
  have hp := (Real.hasStrictDerivAt_const_rpow (h i) a).hasDerivAt
  exact hp.mul_const (effectiveVelocity L lambda i)

omit [Nonempty I] in
/-- The second raw escort numerator has the expected order derivative. -/
theorem hasDerivAt_lineWeightedSecond_order (L : PositiveLineData I)
    (a lambda : ℝ) (h : LinePositive L lambda) :
    HasDerivAt (fun b => lineWeightedSecond L b lambda)
      (lineLogWeightedSecond L a lambda) a := by
  unfold lineWeightedSecond lineLogWeightedSecond
  apply HasDerivAt.fun_sum
  intro i _hi
  have hp := (Real.hasStrictDerivAt_const_rpow (h i) a).hasDerivAt
  exact hp.mul_const ((effectiveVelocity L lambda i) ^ 2)

/-- Exact order derivative of the escort mean. -/
theorem hasDerivAt_escortMean_order (L : PositiveLineData I)
    (a lambda : ℝ) (h : LinePositive L lambda) :
    HasDerivAt (fun b => escortMean L b lambda)
      (escortMeanAlpha L a lambda) a := by
  rw [show (fun b => escortMean L b lambda) =
      fun b => lineWeightedFirst L b lambda / linePowerSum L b lambda by
    funext b
    exact escortMean_eq_lineWeightedFirst_div L b lambda]
  have hq := (hasDerivAt_lineWeightedFirst_order L a lambda h).div
    (hasDerivAt_linePowerSum_order L a lambda h)
    (linePowerSum_pos_all L a h).ne'
  apply hq.congr_deriv
  rw [escortMeanAlpha, escortMean_eq_lineWeightedFirst_div]
  field_simp [(linePowerSum_pos_all L a h).ne']

/-- Exact order derivative of the escort second moment. -/
theorem hasDerivAt_escortSecond_order (L : PositiveLineData I)
    (a lambda : ℝ) (h : LinePositive L lambda) :
    HasDerivAt (fun b => escortSecond L b lambda)
      (escortSecondAlpha L a lambda) a := by
  rw [show (fun b => escortSecond L b lambda) =
      fun b => lineWeightedSecond L b lambda / linePowerSum L b lambda by
    funext b
    exact escortSecond_eq_lineWeightedSecond_div L b lambda]
  have hq := (hasDerivAt_lineWeightedSecond_order L a lambda h).div
    (hasDerivAt_linePowerSum_order L a lambda h)
    (linePowerSum_pos_all L a h).ne'
  apply hq.congr_deriv
  rw [escortSecondAlpha, escortSecond_eq_lineWeightedSecond_div]
  field_simp [(linePowerSum_pos_all L a h).ne']

/-- Exact order derivative of the escort variance. -/
theorem hasDerivAt_escortVar_order (L : PositiveLineData I)
    (a lambda : ℝ) (h : LinePositive L lambda) :
    HasDerivAt (fun b => escortVar L b lambda)
      (escortVarAlpha L a lambda) a := by
  have hs := hasDerivAt_escortSecond_order L a lambda h
  have hm := hasDerivAt_escortMean_order L a lambda h
  have hraw := hs.sub (hm.mul hm)
  have heq : (fun b => escortVar L b lambda) =ᶠ[nhds a]
      fun b => escortSecond L b lambda -
        escortMean L b lambda * escortMean L b lambda := by
    filter_upwards [] with b
    simp only [escortVar]
    ring
  apply (hraw.congr_of_eventuallyEq heq).congr_deriv
  unfold escortVarAlpha
  ring

/-- The explicit escort-mean order derivative is jointly continuous. -/
theorem continuousAt_escortMeanAlpha_pair (L : PositiveLineData I)
    (a lambda : ℝ) (h : LinePositive L lambda) :
    ContinuousAt (fun p : ℝ × ℝ => escortMeanAlpha L p.1 p.2)
      (a, lambda) := by
  unfold escortMeanAlpha lineLogWeightedFirst lineLogPowerSum
  have hP := continuousAt_linePowerSum_pair L a lambda h
  have hPne := (linePowerSum_pos_all L a h).ne'
  have hlog : ∀ i : I, ContinuousAt
      (fun p : ℝ × ℝ => Real.log (lineRaw L p.2 i)) (a, lambda) := by
    intro i
    have hr : ContinuousAt (fun p : ℝ × ℝ => lineRaw L p.2 i)
        (a, lambda) := by
      unfold lineRaw
      fun_prop
    exact hr.log (h i).ne'
  have hLF : ContinuousAt (fun p : ℝ × ℝ =>
      ∑ i, lineRaw L p.2 i ^ p.1 * Real.log (lineRaw L p.2 i) *
        effectiveVelocity L p.2 i) (a, lambda) :=
    tendsto_finsetSum Finset.univ fun i _hi =>
      ((continuousAt_lineRaw_rpow_pair L i a lambda h).mul (hlog i)).mul
        (continuousAt_effectiveVelocity_pair L i a lambda h)
  have hL : ContinuousAt (fun p : ℝ × ℝ =>
      ∑ i, lineRaw L p.2 i ^ p.1 * Real.log (lineRaw L p.2 i))
      (a, lambda) :=
    tendsto_finsetSum Finset.univ fun i _hi =>
      (continuousAt_lineRaw_rpow_pair L i a lambda h).mul (hlog i)
  exact (hLF.div hP hPne).sub
    ((continuousAt_escortMean_pair L a lambda h).mul (hL.div hP hPne))

/-- The explicit escort-second order derivative is jointly continuous. -/
theorem continuousAt_escortSecondAlpha_pair (L : PositiveLineData I)
    (a lambda : ℝ) (h : LinePositive L lambda) :
    ContinuousAt (fun p : ℝ × ℝ => escortSecondAlpha L p.1 p.2)
      (a, lambda) := by
  unfold escortSecondAlpha lineLogWeightedSecond lineLogPowerSum
  have hP := continuousAt_linePowerSum_pair L a lambda h
  have hPne := (linePowerSum_pos_all L a h).ne'
  have hlog : ∀ i : I, ContinuousAt
      (fun p : ℝ × ℝ => Real.log (lineRaw L p.2 i)) (a, lambda) := by
    intro i
    have hr : ContinuousAt (fun p : ℝ × ℝ => lineRaw L p.2 i)
        (a, lambda) := by
      unfold lineRaw
      fun_prop
    exact hr.log (h i).ne'
  have hLS : ContinuousAt (fun p : ℝ × ℝ =>
      ∑ i, lineRaw L p.2 i ^ p.1 * Real.log (lineRaw L p.2 i) *
        (effectiveVelocity L p.2 i) ^ 2) (a, lambda) :=
    tendsto_finsetSum Finset.univ fun i _hi =>
      ((continuousAt_lineRaw_rpow_pair L i a lambda h).mul (hlog i)).mul
        ((continuousAt_effectiveVelocity_pair L i a lambda h).pow 2)
  have hL : ContinuousAt (fun p : ℝ × ℝ =>
      ∑ i, lineRaw L p.2 i ^ p.1 * Real.log (lineRaw L p.2 i))
      (a, lambda) :=
    tendsto_finsetSum Finset.univ fun i _hi =>
      (continuousAt_lineRaw_rpow_pair L i a lambda h).mul (hlog i)
  exact (hLS.div hP hPne).sub
    ((continuousAt_escortSecond_pair L a lambda h).mul (hL.div hP hPne))

/-- The explicit escort-variance order derivative is jointly continuous. -/
theorem continuousAt_escortVarAlpha_pair (L : PositiveLineData I)
    (a lambda : ℝ) (h : LinePositive L lambda) :
    ContinuousAt (fun p : ℝ × ℝ => escortVarAlpha L p.1 p.2)
      (a, lambda) := by
  unfold escortVarAlpha
  exact (continuousAt_escortSecondAlpha_pair L a lambda h).sub
    ((continuousAt_const.mul (continuousAt_escortMean_pair L a lambda h)).mul
      (continuousAt_escortMeanAlpha_pair L a lambda h))

end LocalFiniteParameter

section ClippedFiniteParameter

variable {I : Type u} [Fintype I] [Nonempty I]

/-- Continuous projection of the line parameter onto the compact interval. -/
def lineClip (lambda0 : ℝ) (hlambda0 : 0 < lambda0) (lambda : ℝ) : ℝ :=
  (Set.projIcc (-lambda0) lambda0 (by linarith) lambda : ℝ)

theorem lineClip_mem (lambda0 : ℝ) (hlambda0 : 0 < lambda0) (lambda : ℝ) :
    lineClip lambda0 hlambda0 lambda ∈ Icc (-lambda0) lambda0 :=
  (Set.projIcc (-lambda0) lambda0 (by linarith) lambda).2

theorem lineClip_of_mem {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    {lambda : ℝ} (hlambda : lambda ∈ Icc (-lambda0) lambda0) :
    lineClip lambda0 hlambda0 lambda = lambda := by
  exact congrArg Subtype.val
    (Set.projIcc_of_mem (by linarith : -lambda0 ≤ lambda0) hlambda)

theorem continuous_lineClip (lambda0 : ℝ) (hlambda0 : 0 < lambda0) :
    Continuous (lineClip lambda0 hlambda0) := by
  unfold lineClip
  fun_prop

/-- Entropy numerator evaluated on the globally positive clipped line. -/
def clippedEntropyNumerator (L : PositiveLineData I) (lambda0 : ℝ)
    (hlambda0 : 0 < lambda0) (a lambda : ℝ) : ℝ :=
  Real.log (linePowerSum L a (lineClip lambda0 hlambda0 lambda)) -
    a * Real.log (lineMass L (lineClip lambda0 hlambda0 lambda))

/-- Order derivative of the clipped entropy numerator. -/
def clippedEntropyNumeratorAlpha (L : PositiveLineData I) (lambda0 : ℝ)
    (hlambda0 : 0 < lambda0) (a lambda : ℝ) : ℝ :=
  lineLogPowerSum L a (lineClip lambda0 hlambda0 lambda) /
      linePowerSum L a (lineClip lambda0 hlambda0 lambda) -
    Real.log (lineMass L (lineClip lambda0 hlambda0 lambda))

/-- Numerator whose removable quotient is the first line derivative. -/
def clippedFirstNumerator (L : PositiveLineData I) (lambda0 : ℝ)
    (hlambda0 : 0 < lambda0) (a lambda : ℝ) : ℝ :=
  a * (escortMean L a (lineClip lambda0 hlambda0 lambda) -
    escortMean L 1 (lineClip lambda0 hlambda0 lambda))

/-- Order derivative of the first-derivative numerator. -/
def clippedFirstNumeratorAlpha (L : PositiveLineData I) (lambda0 : ℝ)
    (hlambda0 : 0 < lambda0) (a lambda : ℝ) : ℝ :=
  (escortMean L a (lineClip lambda0 hlambda0 lambda) -
      escortMean L 1 (lineClip lambda0 hlambda0 lambda)) +
    a * escortMeanAlpha L a (lineClip lambda0 hlambda0 lambda)

/-- Numerator whose removable quotient is the second line derivative. -/
def clippedSecondNumerator (L : PositiveLineData I) (lambda0 : ℝ)
    (hlambda0 : 0 < lambda0) (a lambda : ℝ) : ℝ :=
  -a * (1 - a) * escortVar L a (lineClip lambda0 hlambda0 lambda) +
    a * ((escortMean L 1 (lineClip lambda0 hlambda0 lambda)) ^ 2 -
      (escortMean L a (lineClip lambda0 hlambda0 lambda)) ^ 2)

/-- Order derivative of the second-derivative numerator. -/
def clippedSecondNumeratorAlpha (L : PositiveLineData I) (lambda0 : ℝ)
    (hlambda0 : 0 < lambda0) (a lambda : ℝ) : ℝ :=
  (2 * a - 1) * escortVar L a (lineClip lambda0 hlambda0 lambda) -
    a * (1 - a) * escortVarAlpha L a (lineClip lambda0 hlambda0 lambda) +
    ((escortMean L 1 (lineClip lambda0 hlambda0 lambda)) ^ 2 -
      (escortMean L a (lineClip lambda0 hlambda0 lambda)) ^ 2) -
    2 * a * escortMean L a (lineClip lambda0 hlambda0 lambda) *
      escortMeanAlpha L a (lineClip lambda0 hlambda0 lambda)

/-- The clipping map on an order-line pair is continuous. -/
theorem continuous_order_lineClip (lambda0 : ℝ) (hlambda0 : 0 < lambda0) :
    Continuous (fun p : ℝ × ℝ =>
      (p.1, lineClip lambda0 hlambda0 p.2)) := by
  exact continuous_fst.prodMk ((continuous_lineClip lambda0 hlambda0).comp continuous_snd)

/-- Clipped escort means are globally jointly continuous. -/
theorem continuous_clippedEscortMean (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda) :
    Continuous (fun p : ℝ × ℝ =>
      escortMean L p.1 (lineClip lambda0 hlambda0 p.2)) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hmap : ContinuousAt (fun q : ℝ × ℝ =>
      (q.1, lineClip lambda0 hlambda0 q.2)) p :=
    (continuous_order_lineClip lambda0 hlambda0).continuousAt
  change ContinuousAt ((fun q : ℝ × ℝ => escortMean L q.1 q.2) ∘
    fun q : ℝ × ℝ => (q.1, lineClip lambda0 hlambda0 q.2)) p
  exact (continuousAt_escortMean_pair L p.1
      (lineClip lambda0 hlambda0 p.2)
      (hpos _ (lineClip_mem lambda0 hlambda0 p.2))).comp (x := p) hmap

/-- Clipped escort variances are globally jointly continuous. -/
theorem continuous_clippedEscortVar (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda) :
    Continuous (fun p : ℝ × ℝ =>
      escortVar L p.1 (lineClip lambda0 hlambda0 p.2)) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hmap : ContinuousAt (fun q : ℝ × ℝ =>
      (q.1, lineClip lambda0 hlambda0 q.2)) p :=
    (continuous_order_lineClip lambda0 hlambda0).continuousAt
  change ContinuousAt ((fun q : ℝ × ℝ => escortVar L q.1 q.2) ∘
    fun q : ℝ × ℝ => (q.1, lineClip lambda0 hlambda0 q.2)) p
  exact (continuousAt_escortVar_pair L p.1
      (lineClip lambda0 hlambda0 p.2)
      (hpos _ (lineClip_mem lambda0 hlambda0 p.2))).comp (x := p) hmap

/-- Clipped escort-mean order derivatives are globally jointly continuous. -/
theorem continuous_clippedEscortMeanAlpha (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda) :
    Continuous (fun p : ℝ × ℝ =>
      escortMeanAlpha L p.1 (lineClip lambda0 hlambda0 p.2)) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hmap : ContinuousAt (fun q : ℝ × ℝ =>
      (q.1, lineClip lambda0 hlambda0 q.2)) p :=
    (continuous_order_lineClip lambda0 hlambda0).continuousAt
  change ContinuousAt ((fun q : ℝ × ℝ => escortMeanAlpha L q.1 q.2) ∘
    fun q : ℝ × ℝ => (q.1, lineClip lambda0 hlambda0 q.2)) p
  exact (continuousAt_escortMeanAlpha_pair L p.1
      (lineClip lambda0 hlambda0 p.2)
      (hpos _ (lineClip_mem lambda0 hlambda0 p.2))).comp (x := p) hmap

/-- Clipped escort-variance order derivatives are globally jointly continuous. -/
theorem continuous_clippedEscortVarAlpha (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda) :
    Continuous (fun p : ℝ × ℝ =>
      escortVarAlpha L p.1 (lineClip lambda0 hlambda0 p.2)) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hmap : ContinuousAt (fun q : ℝ × ℝ =>
      (q.1, lineClip lambda0 hlambda0 q.2)) p :=
    (continuous_order_lineClip lambda0 hlambda0).continuousAt
  change ContinuousAt ((fun q : ℝ × ℝ => escortVarAlpha L q.1 q.2) ∘
    fun q : ℝ × ℝ => (q.1, lineClip lambda0 hlambda0 q.2)) p
  exact (continuousAt_escortVarAlpha_pair L p.1
      (lineClip lambda0 hlambda0 p.2)
      (hpos _ (lineClip_mem lambda0 hlambda0 p.2))).comp (x := p) hmap

/-- Clipped entropy-numerator order derivatives are globally continuous. -/
theorem continuous_clippedEntropyNumeratorAlpha (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda) :
    Continuous (fun p : ℝ × ℝ =>
      clippedEntropyNumeratorAlpha L lambda0 hlambda0 p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  let c := lineClip lambda0 hlambda0 p.2
  have hc : LinePositive L c := hpos c (lineClip_mem lambda0 hlambda0 p.2)
  have hmap : ContinuousAt (fun q : ℝ × ℝ =>
      (q.1, lineClip lambda0 hlambda0 q.2)) p :=
    (continuous_order_lineClip lambda0 hlambda0).continuousAt
  have hclip : ContinuousAt (fun q : ℝ × ℝ =>
      lineClip lambda0 hlambda0 q.2) p :=
    (continuous_lineClip lambda0 hlambda0).continuousAt.comp (x := p)
      continuousAt_snd
  have hP := (continuousAt_linePowerSum_pair L p.1 c hc).comp (x := p) hmap
  have hraw : ∀ i : I, ContinuousAt
      (fun q : ℝ × ℝ => lineRaw L (lineClip lambda0 hlambda0 q.2) i) p := by
    intro i
    unfold lineRaw
    exact continuousAt_const.mul
      (continuousAt_const.add (continuousAt_const.mul hclip))
  have hLP : ContinuousAt (fun q : ℝ × ℝ =>
      lineLogPowerSum L q.1 (lineClip lambda0 hlambda0 q.2)) p := by
    unfold lineLogPowerSum
    exact tendsto_finsetSum Finset.univ fun i _hi =>
      ((hraw i).rpow continuousAt_fst (Or.inl (hc i).ne')).mul
        ((hraw i).log (hc i).ne')
  have hmass : ContinuousAt (fun q : ℝ × ℝ =>
      lineMass L (lineClip lambda0 hlambda0 q.2)) p := by
    unfold lineMass lineRaw
    exact tendsto_finsetSum Finset.univ fun i _hi => hraw i
  unfold clippedEntropyNumeratorAlpha
  exact hLP.div hP (linePowerSum_pos_all L p.1 hc).ne' |>.sub
    (hmass.log (lineMass_pos L hc).ne')

/-- The clipped first-numerator derivative is globally continuous. -/
theorem continuous_clippedFirstNumeratorAlpha (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda) :
    Continuous (fun p : ℝ × ℝ =>
      clippedFirstNumeratorAlpha L lambda0 hlambda0 p.1 p.2) := by
  unfold clippedFirstNumeratorAlpha
  have hm := continuous_clippedEscortMean L hlambda0 hpos
  have hma := continuous_clippedEscortMeanAlpha L hlambda0 hpos
  have hm1 : Continuous (fun p : ℝ × ℝ =>
      escortMean L 1 (lineClip lambda0 hlambda0 p.2)) := by
    change Continuous ((fun q : ℝ × ℝ =>
      escortMean L q.1 (lineClip lambda0 hlambda0 q.2)) ∘
        fun p : ℝ × ℝ => (1, p.2))
    exact hm.comp (continuous_const.prodMk continuous_snd)
  exact (hm.sub hm1).add (continuous_fst.mul hma)

/-- The clipped second-numerator derivative is globally continuous. -/
theorem continuous_clippedSecondNumeratorAlpha (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda) :
    Continuous (fun p : ℝ × ℝ =>
      clippedSecondNumeratorAlpha L lambda0 hlambda0 p.1 p.2) := by
  unfold clippedSecondNumeratorAlpha
  have hm := continuous_clippedEscortMean L hlambda0 hpos
  have hv := continuous_clippedEscortVar L hlambda0 hpos
  have hma := continuous_clippedEscortMeanAlpha L hlambda0 hpos
  have hva := continuous_clippedEscortVarAlpha L hlambda0 hpos
  have hm1 : Continuous (fun p : ℝ × ℝ =>
      escortMean L 1 (lineClip lambda0 hlambda0 p.2)) := by
    change Continuous ((fun q : ℝ × ℝ =>
      escortMean L q.1 (lineClip lambda0 hlambda0 q.2)) ∘
        fun p : ℝ × ℝ => (1, p.2))
    exact hm.comp (continuous_const.prodMk continuous_snd)
  exact (((continuous_const.mul continuous_fst).sub continuous_const).mul hv).sub
    ((continuous_fst.mul (continuous_const.sub continuous_fst)).mul hva) |>.add
      ((hm1.pow 2).sub (hm.pow 2)) |>.sub
        (((continuous_const.mul continuous_fst).mul hm).mul hma)

/-- Order derivative of the clipped entropy numerator. -/
theorem hasDerivAt_clippedEntropyNumerator (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda)
    (a lambda : ℝ) :
    HasDerivAt (fun b => clippedEntropyNumerator L lambda0 hlambda0 b lambda)
      (clippedEntropyNumeratorAlpha L lambda0 hlambda0 a lambda) a := by
  let c := lineClip lambda0 hlambda0 lambda
  have hc : LinePositive L c := hpos c (lineClip_mem lambda0 hlambda0 lambda)
  unfold clippedEntropyNumerator clippedEntropyNumeratorAlpha
  have hP := hasDerivAt_linePowerSum_order L a c hc
  change HasDerivAt (fun b => Real.log (linePowerSum L b c) -
      b * Real.log (lineMass L c))
    (lineLogPowerSum L a c / linePowerSum L a c - Real.log (lineMass L c)) a
  have hd := (hP.log (linePowerSum_pos_all L a hc).ne').sub
    ((hasDerivAt_id a).mul_const (Real.log (lineMass L c)))
  change HasDerivAt ((fun b => Real.log (linePowerSum L b c)) -
      fun b => id b * Real.log (lineMass L c))
    (lineLogPowerSum L a c / linePowerSum L a c - Real.log (lineMass L c)) a
  apply hd.congr_deriv
  simp only [one_mul]

/-- Order derivative of the clipped first-derivative numerator. -/
theorem hasDerivAt_clippedFirstNumerator (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda)
    (a lambda : ℝ) :
    HasDerivAt (fun b => clippedFirstNumerator L lambda0 hlambda0 b lambda)
      (clippedFirstNumeratorAlpha L lambda0 hlambda0 a lambda) a := by
  let c := lineClip lambda0 hlambda0 lambda
  have hc : LinePositive L c := hpos c (lineClip_mem lambda0 hlambda0 lambda)
  unfold clippedFirstNumerator clippedFirstNumeratorAlpha
  change HasDerivAt (fun b => b * (escortMean L b c - escortMean L 1 c))
    ((escortMean L a c - escortMean L 1 c) +
      a * escortMeanAlpha L a c) a
  have hd := (hasDerivAt_id a).mul
    ((hasDerivAt_escortMean_order L a c hc).sub_const (escortMean L 1 c))
  change HasDerivAt (id * (fun b => escortMean L b c - escortMean L 1 c))
    ((escortMean L a c - escortMean L 1 c) +
      a * escortMeanAlpha L a c) a
  apply hd.congr_deriv
  simp only [one_mul, id_eq]

/-- Order derivative of the clipped second-derivative numerator. -/
theorem hasDerivAt_clippedSecondNumerator (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda)
    (a lambda : ℝ) :
    HasDerivAt (fun b => clippedSecondNumerator L lambda0 hlambda0 b lambda)
      (clippedSecondNumeratorAlpha L lambda0 hlambda0 a lambda) a := by
  let c := lineClip lambda0 hlambda0 lambda
  have hc : LinePositive L c := hpos c (lineClip_mem lambda0 hlambda0 lambda)
  have ha := hasDerivAt_id a
  have hv := hasDerivAt_escortVar_order L a c hc
  have hm := hasDerivAt_escortMean_order L a c hc
  unfold clippedSecondNumerator clippedSecondNumeratorAlpha
  change HasDerivAt (fun b =>
      -b * (1 - b) * escortVar L b c +
        b * ((escortMean L 1 c) ^ 2 - (escortMean L b c) ^ 2))
    ((2 * a - 1) * escortVar L a c -
      a * (1 - a) * escortVarAlpha L a c +
      ((escortMean L 1 c) ^ 2 - (escortMean L a c) ^ 2) -
      2 * a * escortMean L a c * escortMeanAlpha L a c) a
  have hd := ((ha.neg.mul ((hasDerivAt_const a 1).sub ha)).mul hv).add
    (ha.mul ((hasDerivAt_const a ((escortMean L 1 c) ^ 2)).sub
      (hm.pow 2)))
  change HasDerivAt
    ((-id * ((fun _ : ℝ => 1) - id) * fun b => escortVar L b c) +
      id * ((fun _ : ℝ => (escortMean L 1 c) ^ 2) -
        (fun b => escortMean L b c) ^ 2))
    ((2 * a - 1) * escortVar L a c -
      a * (1 - a) * escortVarAlpha L a c +
      ((escortMean L 1 c) ^ 2 - (escortMean L a c) ^ 2) -
      2 * a * escortMean L a c * escortMeanAlpha L a c) a
  apply hd.congr_deriv
  simp [id_eq]
  ring

/-- The mixed derivative definition reduces to the explicit entropy numerator derivative. -/
theorem alphaLambdaDeriv_clippedEntropyNumerator (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda)
    (a lambda : ℝ) :
    alphaLambdaDeriv (fun p => clippedEntropyNumerator L lambda0 hlambda0 p.1 p.2)
        0 a lambda =
      clippedEntropyNumeratorAlpha L lambda0 hlambda0 a lambda := by
  exact (hasDerivAt_clippedEntropyNumerator L hlambda0 hpos a lambda).deriv

/-- The mixed derivative definition reduces to the explicit first numerator derivative. -/
theorem alphaLambdaDeriv_clippedFirstNumerator (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda)
    (a lambda : ℝ) :
    alphaLambdaDeriv (fun p => clippedFirstNumerator L lambda0 hlambda0 p.1 p.2)
        0 a lambda =
      clippedFirstNumeratorAlpha L lambda0 hlambda0 a lambda := by
  exact (hasDerivAt_clippedFirstNumerator L hlambda0 hpos a lambda).deriv

/-- The mixed derivative definition reduces to the explicit second numerator derivative. -/
theorem alphaLambdaDeriv_clippedSecondNumerator (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda)
    (a lambda : ℝ) :
    alphaLambdaDeriv (fun p => clippedSecondNumerator L lambda0 hlambda0 p.1 p.2)
        0 a lambda =
      clippedSecondNumeratorAlpha L lambda0 hlambda0 a lambda := by
  exact (hasDerivAt_clippedSecondNumerator L hlambda0 hpos a lambda).deriv

/-- A globally continuous removable quotient follows by applying the compact
parameterized theorem on a closed ball around each point. -/
theorem continuous_removableShannonQuotient_of_global
    (F : ℝ × ℝ → ℝ)
    (hFone : ∀ lambda, F (1, lambda) = 0)
    (hmixed : Continuous
      (fun p : ℝ × ℝ => alphaLambdaDeriv F 0 p.1 p.2))
    (hderiv : ∀ a lambda, HasDerivAt (fun b => F (b, lambda))
      (alphaLambdaDeriv F 0 a lambda) a) :
    Continuous (fun p : ℝ × ℝ =>
      removableShannonQuotient F p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hcompact : IsCompact (Metric.closedBall p 1) :=
    isCompact_closedBall p 1
  have hlocal := continuousOn_removableShannonQuotient F hcompact
    hFone hmixed hderiv
  exact hlocal.continuousAt (Metric.closedBall_mem_nhds p zero_lt_one)

/-- The clipped entropy removable quotient is globally continuous. -/
theorem continuous_clippedEntropyQuotient (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda) :
    Continuous (fun p : ℝ × ℝ => removableShannonQuotient
      (fun q => clippedEntropyNumerator L lambda0 hlambda0 q.1 q.2)
      p.1 p.2) := by
  apply continuous_removableShannonQuotient_of_global
  · intro lambda
    simp [clippedEntropyNumerator, linePowerSum_one]
  · convert continuous_clippedEntropyNumeratorAlpha L hlambda0 hpos using 1
    ext p
    exact alphaLambdaDeriv_clippedEntropyNumerator L hlambda0 hpos p.1 p.2
  · intro a lambda
    rw [alphaLambdaDeriv_clippedEntropyNumerator L hlambda0 hpos]
    exact hasDerivAt_clippedEntropyNumerator L hlambda0 hpos a lambda

/-- The clipped first-derivative removable quotient is globally continuous. -/
theorem continuous_clippedFirstQuotient (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda) :
    Continuous (fun p : ℝ × ℝ => removableShannonQuotient
      (fun q => clippedFirstNumerator L lambda0 hlambda0 q.1 q.2)
      p.1 p.2) := by
  apply continuous_removableShannonQuotient_of_global
  · intro lambda
    simp [clippedFirstNumerator]
  · convert continuous_clippedFirstNumeratorAlpha L hlambda0 hpos using 1
    ext p
    exact alphaLambdaDeriv_clippedFirstNumerator L hlambda0 hpos p.1 p.2
  · intro a lambda
    rw [alphaLambdaDeriv_clippedFirstNumerator L hlambda0 hpos]
    exact hasDerivAt_clippedFirstNumerator L hlambda0 hpos a lambda

/-- The clipped second-derivative removable quotient is globally continuous. -/
theorem continuous_clippedSecondQuotient (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda) :
    Continuous (fun p : ℝ × ℝ => removableShannonQuotient
      (fun q => clippedSecondNumerator L lambda0 hlambda0 q.1 q.2)
      p.1 p.2) := by
  apply continuous_removableShannonQuotient_of_global
  · intro lambda
    simp [clippedSecondNumerator]
  · convert continuous_clippedSecondNumeratorAlpha L hlambda0 hpos using 1
    ext p
    exact alphaLambdaDeriv_clippedSecondNumerator L hlambda0 hpos p.1 p.2
  · intro a lambda
    rw [alphaLambdaDeriv_clippedSecondNumerator L hlambda0 hpos]
    exact hasDerivAt_clippedSecondNumerator L hlambda0 hpos a lambda

/-- The entropy numerator's order derivative at one is minus Shannon entropy. -/
theorem neg_clippedEntropyNumeratorAlpha_one (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda)
    (lambda : ℝ) :
    -clippedEntropyNumeratorAlpha L lambda0 hlambda0 1 lambda =
      entropyLine L 1 (lineClip lambda0 hlambda0 lambda) := by
  let c := lineClip lambda0 hlambda0 lambda
  have hc : LinePositive L c := hpos c (lineClip_mem lambda0 hlambda0 lambda)
  have hsum : ∑ i, lineRaw L c i / lineMass L c = 1 := by
    simpa only [lineProb_apply_of_positive L hc, l1Mass] using
      (lineProb L c).2.2
  unfold clippedEntropyNumeratorAlpha
  change -(lineLogPowerSum L 1 c / linePowerSum L 1 c -
      Real.log (lineMass L c)) = entropyLine L 1 c
  rw [entropyLine, renyi_at_one]
  unfold renyiOne lineLogPowerSum
  rw [linePowerSum_one]
  simp_rw [Real.rpow_one]
  simp_rw [lineProb_apply_of_positive L hc]
  simp_rw [Real.log_div (hc _).ne' (lineMass_pos L hc).ne']
  congr 1
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  rw [hsum, one_mul]
  rw [Finset.sum_div]
  have hsumeq :
      (∑ i, lineRaw L c i * Real.log (lineRaw L c i) /
        lineMass L c) =
      ∑ i, lineRaw L c i / lineMass L c *
        Real.log (lineRaw L c i) := by
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hsumeq]

/-- At the Shannon order, the order derivative of the escort mean is the
negative Shannon line slope. -/
theorem escortMeanAlpha_one_eq_neg_shannonLineSlope
    (L : PositiveLineData I) {lambda : ℝ} (h : LinePositive L lambda) :
    escortMeanAlpha L 1 lambda = -shannonLineSlope L lambda := by
  have hcenter : ∑ i, lineRaw L lambda i / lineMass L lambda *
      (effectiveVelocity L lambda i - escortMean L 1 lambda) = 0 := by
    simpa only [lineProb_apply_of_positive L h, centeredVelocity] using
      sum_lineProb_mul_centeredVelocity_eq_zero L h
  have hleft : escortMeanAlpha L 1 lambda =
      (∑ i, lineRaw L lambda i / lineMass L lambda *
        Real.log (lineRaw L lambda i) * effectiveVelocity L lambda i) -
      escortMean L 1 lambda *
        (∑ i, lineRaw L lambda i / lineMass L lambda *
          Real.log (lineRaw L lambda i)) := by
    unfold escortMeanAlpha lineLogWeightedFirst lineLogPowerSum
    rw [linePowerSum_one]
    simp_rw [Real.rpow_one]
    rw [Finset.sum_div, Finset.sum_div]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _hi
      ring
    · congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      ring
  rw [hleft]
  unfold shannonLineSlope
  simp_rw [lineProb_apply_of_positive L h]
  simp_rw [Real.log_div (h _).ne' (lineMass_pos L h).ne']
  rw [neg_neg]
  have hrawcenter :
      (∑ i, lineRaw L lambda i / lineMass L lambda *
        Real.log (lineRaw L lambda i) * effectiveVelocity L lambda i) -
        escortMean L 1 lambda *
          (∑ i, lineRaw L lambda i / lineMass L lambda *
            Real.log (lineRaw L lambda i)) =
      ∑ i, lineRaw L lambda i / lineMass L lambda *
        (effectiveVelocity L lambda i - escortMean L 1 lambda) *
          Real.log (lineRaw L lambda i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hrawcenter]
  have hcenter' : ∑ i,
      (lineRaw L lambda i / lineMass L lambda * effectiveVelocity L lambda i -
        lineRaw L lambda i / lineMass L lambda * escortMean L 1 lambda) = 0 := by
    rw [← hcenter]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  rw [hcenter', zero_mul, sub_zero]

/-- The first-derivative numerator has the required Shannon endpoint value. -/
theorem neg_clippedFirstNumeratorAlpha_one (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda)
    (lambda : ℝ) :
    -clippedFirstNumeratorAlpha L lambda0 hlambda0 1 lambda =
      entropyLineFirst L 1 (lineClip lambda0 hlambda0 lambda) := by
  let c := lineClip lambda0 hlambda0 lambda
  have hc : LinePositive L c := hpos c (lineClip_mem lambda0 hlambda0 lambda)
  rw [entropyLineFirst_one L hc]
  unfold clippedFirstNumeratorAlpha
  change -((escortMean L 1 c - escortMean L 1 c) +
      1 * escortMeanAlpha L 1 c) = shannonLineSlope L c
  rw [escortMeanAlpha_one_eq_neg_shannonLineSlope L hc]
  ring

/-- The second-derivative numerator has the required Shannon endpoint value. -/
theorem neg_clippedSecondNumeratorAlpha_one (L : PositiveLineData I)
    {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda)
    (lambda : ℝ) :
    -clippedSecondNumeratorAlpha L lambda0 hlambda0 1 lambda =
      entropyLineSecond L 1 (lineClip lambda0 hlambda0 lambda) := by
  let c := lineClip lambda0 hlambda0 lambda
  have hc : LinePositive L c := hpos c (lineClip_mem lambda0 hlambda0 lambda)
  rw [entropyLineSecond_one L hc]
  unfold clippedSecondNumeratorAlpha
  change -((2 * 1 - 1) * escortVar L 1 c -
      1 * (1 - 1) * escortVarAlpha L 1 c +
      ((escortMean L 1 c) ^ 2 - (escortMean L 1 c) ^ 2) -
      2 * 1 * escortMean L 1 c * escortMeanAlpha L 1 c) =
    -escortVar L 1 c -
      2 * escortMean L 1 c * shannonLineSlope L c
  rw [escortMeanAlpha_one_eq_neg_shannonLineSlope L hc]
  ring

/-- The entropy removable quotient agrees with the endpoint-aware finite
parameter on the positive compact line interval. -/
theorem clippedEntropyQuotient_eq_entropyLine_finite
    (L : PositiveLineData I) {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda)
    {a lambda : ℝ} (ha : 0 ≤ a)
    (hlambda : lambda ∈ Icc (-lambda0) lambda0) :
    removableShannonQuotient
        (fun q => clippedEntropyNumerator L lambda0 hlambda0 q.1 q.2)
        a lambda = entropyLine L (finiteParam a) lambda := by
  by_cases ha0 : a = 0
  · subst a
    rw [removableShannonQuotient_of_ne _ zero_ne_one]
    rw [finiteParam_zero, entropyLine_zero_of_positive L (hpos lambda hlambda)]
    simp [clippedEntropyNumerator, lineClip_of_mem hlambda0 hlambda,
      linePowerSum]
  by_cases ha1 : a = 1
  · subst a
    rw [removableShannonQuotient_one,
      alphaLambdaDeriv_clippedEntropyNumerator L hlambda0 hpos,
      neg_clippedEntropyNumeratorAlpha_one L hlambda0 hpos,
      lineClip_of_mem hlambda0 hlambda, finiteParam_one]
  · rw [removableShannonQuotient_of_ne _ ha1]
    rw [entropyLine_finite_eq_formula L (lt_of_le_of_ne ha (Ne.symm ha0)) ha1
      (hpos lambda hlambda)]
    unfold clippedEntropyNumerator finiteEntropyLineFormula
    rw [lineClip_of_mem hlambda0 hlambda]

/-- The first-derivative removable quotient agrees with the endpoint-aware
finite parameter on the positive compact line interval. -/
theorem clippedFirstQuotient_eq_entropyLineFirst_finite
    (L : PositiveLineData I) {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda)
    {a lambda : ℝ} (ha : 0 ≤ a)
    (hlambda : lambda ∈ Icc (-lambda0) lambda0) :
    removableShannonQuotient
        (fun q => clippedFirstNumerator L lambda0 hlambda0 q.1 q.2)
        a lambda = entropyLineFirst L (finiteParam a) lambda := by
  by_cases ha0 : a = 0
  · subst a
    rw [removableShannonQuotient_of_ne _ zero_ne_one]
    simp [clippedFirstNumerator, finiteParam_zero,
      entropyLineFirst_zero L (hpos lambda hlambda)]
  by_cases ha1 : a = 1
  · subst a
    rw [removableShannonQuotient_one,
      alphaLambdaDeriv_clippedFirstNumerator L hlambda0 hpos,
      neg_clippedFirstNumeratorAlpha_one L hlambda0 hpos,
      lineClip_of_mem hlambda0 hlambda, finiteParam_one]
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    rw [removableShannonQuotient_of_ne _ ha1]
    rw [entropyLineFirst_finite_on L (isOpen_setOf_linePositive L)
      (fun s hs => hs) hapos ha1 (hpos lambda hlambda)]
    rw [singularWeight_finite ha ha1]
    unfold clippedFirstNumerator
    rw [lineClip_of_mem hlambda0 hlambda]
    field_simp [sub_ne_zero.mpr (Ne.symm ha1)]

/-- The second-derivative removable quotient agrees with the endpoint-aware
finite parameter on the positive compact line interval. -/
theorem clippedSecondQuotient_eq_entropyLineSecond_finite
    (L : PositiveLineData I) {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda)
    {a lambda : ℝ} (ha : 0 ≤ a)
    (hlambda : lambda ∈ Icc (-lambda0) lambda0) :
    removableShannonQuotient
        (fun q => clippedSecondNumerator L lambda0 hlambda0 q.1 q.2)
        a lambda = entropyLineSecond L (finiteParam a) lambda := by
  by_cases ha0 : a = 0
  · subst a
    rw [removableShannonQuotient_of_ne _ zero_ne_one]
    simp [clippedSecondNumerator, finiteParam_zero,
      entropyLineSecond_zero L (hpos lambda hlambda)]
  by_cases ha1 : a = 1
  · subst a
    rw [removableShannonQuotient_one,
      alphaLambdaDeriv_clippedSecondNumerator L hlambda0 hpos,
      neg_clippedSecondNumeratorAlpha_one L hlambda0 hpos,
      lineClip_of_mem hlambda0 hlambda, finiteParam_one]
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    rw [removableShannonQuotient_of_ne _ ha1]
    rw [entropyLineSecond_finite_on L (isOpen_setOf_linePositive L)
      (fun s hs => hs) hapos ha1 (hpos lambda hlambda)]
    rw [singularWeight_finite ha ha1]
    unfold clippedSecondNumerator
    rw [lineClip_of_mem hlambda0 hlambda]
    field_simp [sub_ne_zero.mpr (Ne.symm ha1)]

/-! ### Continuity at every finite compactified order -/

/-- Joint continuity of the three endpoint-aware line quantities at every
finite parameter, including the removable orders zero and one. -/
theorem continuousWithinAt_entropyLine_bundle_of_ne_top
    (L : PositiveLineData I) {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda)
    {a : Param} (ha : a ≠ ⊤) {lambda : ℝ}
    (hlambda : lambda ∈ Icc (-lambda0) lambda0) :
    ContinuousWithinAt (fun p : Param × ℝ => entropyLine L p.1 p.2)
        (Set.univ ×ˢ Icc (-lambda0) lambda0) (a, lambda) ∧
      ContinuousWithinAt (fun p : Param × ℝ => entropyLineFirst L p.1 p.2)
        (Set.univ ×ˢ Icc (-lambda0) lambda0) (a, lambda) ∧
      ContinuousWithinAt (fun p : Param × ℝ => entropyLineSecond L p.1 p.2)
        (Set.univ ×ˢ Icc (-lambda0) lambda0) (a, lambda) := by
  let R : Param × ℝ → ℝ × ℝ := fun p => (ENNReal.toReal p.1, p.2)
  have hto : ContinuousAt ENNReal.toReal a := ENNReal.tendsto_toReal ha
  have hR : ContinuousAt R (a, lambda) := by
    exact (hto.comp (x := (a, lambda)) continuousAt_fst).prodMk continuousAt_snd
  have hane : {b : Param | b ≠ ⊤} ∈ 𝓝 a :=
    ENNReal.isOpen_ne_top.mem_nhds ha
  have hfinite : ∀ᶠ p : Param × ℝ in 𝓝 (a, lambda), p.1 ≠ ⊤ := by
    have hfst : ContinuousAt (fun p : Param × ℝ => p.1) (a, lambda) :=
      continuousAt_fst
    exact hfst hane
  have hfiniteWithin : ∀ᶠ p : Param × ℝ in
      𝓝[Set.univ ×ˢ Icc (-lambda0) lambda0] (a, lambda), p.1 ≠ ⊤ :=
    hfinite.filter_mono inf_le_left
  have hreconstruct (b : Param) (hb : b ≠ ⊤) :
      finiteParam (ENNReal.toReal b) = b := ENNReal.ofReal_toReal hb
  have hnonneg (b : Param) : 0 ≤ ENNReal.toReal b := ENNReal.toReal_nonneg
  have hEntropy : ContinuousAt (fun p : Param × ℝ =>
      removableShannonQuotient
        (fun q => clippedEntropyNumerator L lambda0 hlambda0 q.1 q.2)
        (ENNReal.toReal p.1) p.2) (a, lambda) := by
    change ContinuousAt ((fun q : ℝ × ℝ => removableShannonQuotient
      (fun z => clippedEntropyNumerator L lambda0 hlambda0 z.1 z.2)
      q.1 q.2) ∘ R) (a, lambda)
    exact (continuous_clippedEntropyQuotient L hlambda0 hpos).continuousAt.comp
      (x := (a, lambda)) hR
  have hFirst : ContinuousAt (fun p : Param × ℝ =>
      removableShannonQuotient
        (fun q => clippedFirstNumerator L lambda0 hlambda0 q.1 q.2)
        (ENNReal.toReal p.1) p.2) (a, lambda) := by
    change ContinuousAt ((fun q : ℝ × ℝ => removableShannonQuotient
      (fun z => clippedFirstNumerator L lambda0 hlambda0 z.1 z.2)
      q.1 q.2) ∘ R) (a, lambda)
    exact (continuous_clippedFirstQuotient L hlambda0 hpos).continuousAt.comp
      (x := (a, lambda)) hR
  have hSecond : ContinuousAt (fun p : Param × ℝ =>
      removableShannonQuotient
        (fun q => clippedSecondNumerator L lambda0 hlambda0 q.1 q.2)
        (ENNReal.toReal p.1) p.2) (a, lambda) := by
    change ContinuousAt ((fun q : ℝ × ℝ => removableShannonQuotient
      (fun z => clippedSecondNumerator L lambda0 hlambda0 z.1 z.2)
      q.1 q.2) ∘ R) (a, lambda)
    exact (continuous_clippedSecondQuotient L hlambda0 hpos).continuousAt.comp
      (x := (a, lambda)) hR
  have hEntropyEq : (fun p : Param × ℝ => entropyLine L p.1 p.2) =ᶠ[
      𝓝[Set.univ ×ˢ Icc (-lambda0) lambda0] (a, lambda)]
      fun p => removableShannonQuotient
        (fun q => clippedEntropyNumerator L lambda0 hlambda0 q.1 q.2)
        (ENNReal.toReal p.1) p.2 := by
    filter_upwards [hfiniteWithin, self_mem_nhdsWithin] with p hpfin hpK
    rw [clippedEntropyQuotient_eq_entropyLine_finite L hlambda0 hpos
      (hnonneg p.1) hpK.2, hreconstruct p.1 hpfin]
  have hFirstEq : (fun p : Param × ℝ => entropyLineFirst L p.1 p.2) =ᶠ[
      𝓝[Set.univ ×ˢ Icc (-lambda0) lambda0] (a, lambda)]
      fun p => removableShannonQuotient
        (fun q => clippedFirstNumerator L lambda0 hlambda0 q.1 q.2)
        (ENNReal.toReal p.1) p.2 := by
    filter_upwards [hfiniteWithin, self_mem_nhdsWithin] with p hpfin hpK
    rw [clippedFirstQuotient_eq_entropyLineFirst_finite L hlambda0 hpos
      (hnonneg p.1) hpK.2, hreconstruct p.1 hpfin]
  have hSecondEq : (fun p : Param × ℝ => entropyLineSecond L p.1 p.2) =ᶠ[
      𝓝[Set.univ ×ˢ Icc (-lambda0) lambda0] (a, lambda)]
      fun p => removableShannonQuotient
        (fun q => clippedSecondNumerator L lambda0 hlambda0 q.1 q.2)
        (ENNReal.toReal p.1) p.2 := by
    filter_upwards [hfiniteWithin, self_mem_nhdsWithin] with p hpfin hpK
    rw [clippedSecondQuotient_eq_entropyLineSecond_finite L hlambda0 hpos
      (hnonneg p.1) hpK.2, hreconstruct p.1 hpfin]
  refine ⟨hEntropy.continuousWithinAt.congr_of_eventuallyEq hEntropyEq ?_,
    hFirst.continuousWithinAt.congr_of_eventuallyEq hFirstEq ?_,
    hSecond.continuousWithinAt.congr_of_eventuallyEq hSecondEq ?_⟩
  · rw [clippedEntropyQuotient_eq_entropyLine_finite L hlambda0 hpos
      (hnonneg a) hlambda, hreconstruct a ha]
  · rw [clippedFirstQuotient_eq_entropyLineFirst_finite L hlambda0 hpos
      (hnonneg a) hlambda, hreconstruct a ha]
  · rw [clippedSecondQuotient_eq_entropyLineSecond_finite L hlambda0 hpos
      (hnonneg a) hlambda, hreconstruct a ha]

/-! ### Exponential order decay at the upper endpoint -/

/-- Total extension of `r * rho ^ r` to the compactified upper endpoint. -/
def topRpowDecay (rho : ℝ) (a : Param) : ℝ :=
  if _h : a = ⊤ then 0 else ENNReal.toReal a * rho ^ ENNReal.toReal a

@[simp] theorem topRpowDecay_top (rho : ℝ) :
    topRpowDecay rho (⊤ : Param) = 0 := by
  simp [topRpowDecay]

/-- Exponential decay beats the linear order factor at the compactified
upper endpoint. -/
theorem continuousAt_topRpowDecay_top {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    ContinuousAt (topRpowDecay rho) (⊤ : Param) := by
  have hlog : 0 < -Real.log rho := neg_pos.mpr (Real.log_neg hrho0 hrho1)
  have hreal : Tendsto (fun r : ℝ => r * rho ^ r) atTop (𝓝 0) := by
    simpa [Real.rpow_one, Real.rpow_def_of_pos hrho0] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (-Real.log rho) hlog
  change Tendsto (topRpowDecay rho) (𝓝 (⊤ : Param)) (𝓝 0)
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hevent : ∀ᶠ r : ℝ in atTop,
      dist (r * rho ^ r) 0 < epsilon :=
    (Metric.tendsto_nhds.mp hreal) epsilon hepsilon
  rcases (eventually_atTop.1 hevent) with ⟨R, hR⟩
  change {a : Param | dist (topRpowDecay rho a) 0 < epsilon} ∈ 𝓝 ⊤
  rw [nhds_top_basis.mem_iff]
  refine ⟨finiteParam (max R 0),
    lt_top_iff_ne_top.mpr (finiteParam_ne_top _), ?_⟩
  intro a ha
  by_cases hatop : a = ⊤
  · subst a
    simpa [topRpowDecay] using hepsilon
  · have hrealgt : max R 0 < ENNReal.toReal a := by
      exact (ENNReal.ofReal_lt_iff_lt_toReal (le_max_right R 0) hatop).mp ha
    have hdecay := hR (ENNReal.toReal a)
      (le_trans (le_max_left R 0) hrealgt.le)
    simpa [topRpowDecay, hatop] using hdecay

/-- Extend a real function with limit zero at `+infinity` by zero on the
compactified endpoint. -/
def compactifyZeroAtTop (f : ℝ → ℝ) (a : Param) : ℝ :=
  if _htop : a = ⊤ then 0 else f (ENNReal.toReal a)

/-- Any real function tending to zero at `+infinity` has a continuous zero
extension to `Param`. -/
theorem continuousAt_compactifyZeroAtTop (f : ℝ → ℝ)
    (hf : Tendsto f atTop (𝓝 0)) :
    ContinuousAt (compactifyZeroAtTop f) (⊤ : Param) := by
  change Tendsto (compactifyZeroAtTop f) (𝓝 (⊤ : Param)) (𝓝 0)
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hevent : ∀ᶠ r : ℝ in atTop, dist (f r) 0 < epsilon :=
    (Metric.tendsto_nhds.mp hf) epsilon hepsilon
  rcases eventually_atTop.1 hevent with ⟨R, hR⟩
  change {a : Param | dist (compactifyZeroAtTop f a) 0 < epsilon} ∈ 𝓝 ⊤
  rw [nhds_top_basis.mem_iff]
  refine ⟨finiteParam (max R 0),
    lt_top_iff_ne_top.mpr (finiteParam_ne_top _), ?_⟩
  intro a ha
  by_cases hatop : a = ⊤
  · subst a
    simpa [compactifyZeroAtTop] using hepsilon
  · have hrealgt : max R 0 < ENNReal.toReal a :=
      (ENNReal.ofReal_lt_iff_lt_toReal (le_max_right R 0) hatop).mp ha
    have hbound := hR (ENNReal.toReal a)
      (le_trans (le_max_left R 0) hrealgt.le)
    simpa [compactifyZeroAtTop, hatop] using hbound

/-- The singular finite-order coefficient is continuous at the compactified
upper endpoint, where its value is `-1`. -/
theorem continuousAt_singularWeight_top :
    ContinuousAt singularWeight (⊤ : Param) := by
  let f : ℝ → ℝ := fun r => (r - 1)⁻¹
  have hshift : Tendsto (fun r : ℝ => r - 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b + 1, ?_⟩
    intro r hr
    linarith
  have hf : Tendsto f atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hshift
  let g : Param → ℝ := fun a => -1 - compactifyZeroAtTop f a
  have hg : ContinuousAt g (⊤ : Param) := by
    dsimp only [g]
    exact continuousAt_const.sub (continuousAt_compactifyZeroAtTop f hf)
  have honeNhds : Ioi (1 : Param) ∈ 𝓝 (⊤ : Param) := by
    rw [nhds_top_basis.mem_iff]
    exact ⟨1, lt_top_iff_ne_top.mpr (by norm_num), Subset.rfl⟩
  have heq : singularWeight =ᶠ[𝓝 (⊤ : Param)] g := by
    filter_upwards [honeNhds] with a ha
    by_cases hatop : a = ⊤
    · subst a
      simp [g, compactifyZeroAtTop]
    · have hrgt : 1 < ENNReal.toReal a := by
        have ha' : finiteParam 1 < a := by simpa using ha
        exact (ENNReal.ofReal_lt_iff_lt_toReal zero_le_one hatop).mp ha'
      have hr1 : ENNReal.toReal a ≠ 1 := ne_of_gt hrgt
      rw [singularWeight, dif_neg hatop]
      change (if ENNReal.toReal a = 1 then 0 else
        ENNReal.toReal a / (1 - ENNReal.toReal a)) = g a
      rw [if_neg hr1]
      simp [g, compactifyZeroAtTop, f, hatop]
      field_simp [sub_ne_zero.mpr hr1]
      ring
  exact hg.congr_of_eventuallyEq heq

/-! ### Fixed-max geometry and escort bounds -/

omit [Fintype I] [Nonempty I] in
/-- A coordinate tied with the fixed maximizer at one positive point is the
same affine raw coordinate everywhere. -/
theorem fixedMax_tie_lineRaw_eq (L : PositiveLineData I) {K : Set ℝ}
    {istar i : I} (hfixed : FixedMaxCoordinate L K istar)
    {lambda : ℝ} (hlambda : lambda ∈ K)
    (htie : lineRaw L lambda i = lineRaw L lambda istar) (s : ℝ) :
    lineRaw L s i = lineRaw L s istar := by
  have hp := (hfixed lambda hlambda).1
  have hvel := (hfixed lambda hlambda).2.2 i htie
  have hslope : L.x i * L.u i = L.x istar * L.u istar := by
    calc
      L.x i * L.u i = lineRaw L lambda i * effectiveVelocity L lambda i :=
        (lineRaw_mul_effectiveVelocity L hp i).symm
      _ = lineRaw L lambda istar * effectiveVelocity L lambda istar := by
        rw [htie, hvel]
      _ = L.x istar * L.u istar := lineRaw_mul_effectiveVelocity L hp istar
  calc
    lineRaw L s i = lineRaw L lambda i + (s - lambda) * (L.x i * L.u i) := by
      unfold lineRaw
      ring
    _ = lineRaw L lambda istar +
        (s - lambda) * (L.x istar * L.u istar) := by rw [htie, hslope]
    _ = lineRaw L s istar := by
      unfold lineRaw
      ring

omit [Fintype I] [Nonempty I] in
/-- Tied coordinates also have identical effective velocity at every positive
point. -/
theorem fixedMax_tie_effectiveVelocity_eq (L : PositiveLineData I)
    {K : Set ℝ} {istar i : I} (hfixed : FixedMaxCoordinate L K istar)
    {lambda : ℝ} (hlambda : lambda ∈ K)
    (htie : lineRaw L lambda i = lineRaw L lambda istar)
    {s : ℝ} (hs : LinePositive L s) :
    effectiveVelocity L s i = effectiveVelocity L s istar := by
  have hp := (hfixed lambda hlambda).1
  have hvel := (hfixed lambda hlambda).2.2 i htie
  have hslope : L.x i * L.u i = L.x istar * L.u istar := by
    calc
      L.x i * L.u i = lineRaw L lambda i * effectiveVelocity L lambda i :=
        (lineRaw_mul_effectiveVelocity L hp i).symm
      _ = lineRaw L lambda istar * effectiveVelocity L lambda istar := by
        rw [htie, hvel]
      _ = L.x istar * L.u istar := lineRaw_mul_effectiveVelocity L hp istar
  have hraw := fixedMax_tie_lineRaw_eq L hfixed hlambda htie s
  have hprod : lineRaw L s i * effectiveVelocity L s i =
      lineRaw L s i * effectiveVelocity L s istar := by
    calc
      lineRaw L s i * effectiveVelocity L s i = L.x i * L.u i :=
        lineRaw_mul_effectiveVelocity L hs i
      _ = L.x istar * L.u istar := hslope
      _ = lineRaw L s istar * effectiveVelocity L s istar :=
        (lineRaw_mul_effectiveVelocity L hs istar).symm
      _ = lineRaw L s i * effectiveVelocity L s istar := by rw [hraw]
  nlinarith [hs i]

omit [Nonempty I] in
/-- One escort weight is bounded by its raw ratio to any comparison
coordinate. -/
theorem escortWeight_le_ratio_rpow (L : PositiveLineData I)
    {a lambda : ℝ} (_ha : 0 ≤ a) (h : LinePositive L lambda)
    (i istar : I) :
    escortWeight L a lambda i ≤
      (lineRaw L lambda i / lineRaw L lambda istar) ^ a := by
  have hden : lineRaw L lambda istar ^ a ≤ linePowerSum L a lambda := by
    unfold linePowerSum
    exact Finset.single_le_sum
      (fun j _hj => Real.rpow_nonneg (h j).le a) (Finset.mem_univ istar)
  unfold escortWeight
  calc
    lineRaw L lambda i ^ a / linePowerSum L a lambda ≤
        lineRaw L lambda i ^ a / lineRaw L lambda istar ^ a :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg (h i).le a)
        (Real.rpow_pos_of_pos (h istar) a) hden
    _ = (lineRaw L lambda i / lineRaw L lambda istar) ^ a := by
      rw [Real.div_rpow (h i).le (h istar).le]

/-- One centered escort-moment summand, extended by zero at the upper order
endpoint.  `withOrder` inserts the extra order factor needed for the variance
limit. -/
def topEscortMomentTerm (L : PositiveLineData I) (istar i : I)
    (withOrder : Bool) (m : ℕ) (p : Param × ℝ) : ℝ :=
  if _htop : p.1 = ⊤ then 0
  else
    (if withOrder then ENNReal.toReal p.1 else 1) *
      escortWeight L (ENNReal.toReal p.1) p.2 i *
        (effectiveVelocity L p.2 i - effectiveVelocity L p.2 istar) ^ m

omit [Nonempty I] in
@[simp] theorem topEscortMomentTerm_top (L : PositiveLineData I)
    (istar i : I) (withOrder : Bool) (m : ℕ) (lambda : ℝ) :
    topEscortMomentTerm L istar i withOrder m (⊤, lambda) = 0 := by
  simp [topEscortMomentTerm]

/-- Every positive centered escort moment, with or without one order factor,
vanishes jointly at a fixed-max upper endpoint. -/
theorem tendsto_topEscortMomentTerm_fixedMax
    (L : PositiveLineData I) {K : Set ℝ} {istar i : I}
    (hfixed : FixedMaxCoordinate L K istar)
    {lambda : ℝ} (hlambda : lambda ∈ K) {m : ℕ} (hm : 0 < m)
    (withOrder : Bool) :
    Tendsto (topEscortMomentTerm L istar i withOrder m)
      (𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda)) (𝓝 0) := by
  have hp := (hfixed lambda hlambda).1
  by_cases htie : lineRaw L lambda i = lineRaw L lambda istar
  · have heq : topEscortMomentTerm L istar i withOrder m =ᶠ[
        𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda)] fun _ => 0 := by
      filter_upwards [self_mem_nhdsWithin] with p hpK
      by_cases htop : p.1 = ⊤
      · simp [topEscortMomentTerm, htop]
      · have hposp := (hfixed p.2 hpK.2).1
        have hvel := fixedMax_tie_effectiveVelocity_eq L hfixed hlambda htie hposp
        simp [topEscortMomentTerm, htop, hvel, zero_pow hm.ne']
    exact tendsto_const_nhds.congr' heq.symm
  · have hlt : lineRaw L lambda i < lineRaw L lambda istar :=
      lt_of_le_of_ne ((hfixed lambda hlambda).2.1 i) htie
    let ratio : ℝ → ℝ := fun s => lineRaw L s i / lineRaw L s istar
    let rho : ℝ := (ratio lambda + 1) / 2
    have hratio0 : 0 < ratio lambda := div_pos (hp i) (hp istar)
    have hratio1 : ratio lambda < 1 := (div_lt_one (hp istar)).mpr hlt
    have hrho0 : 0 < rho := by
      dsimp only [rho]
      linarith
    have hrho1 : rho < 1 := by
      dsimp only [rho]
      linarith
    have hratioRho : ratio lambda < rho := by
      dsimp only [rho]
      linarith
    have hratioCont : ContinuousAt ratio lambda := by
      dsimp only [ratio]
      have hi : ContinuousAt (fun s => lineRaw L s i) lambda := by
        unfold lineRaw
        fun_prop
      have hs : ContinuousAt (fun s => lineRaw L s istar) lambda := by
        unfold lineRaw
        fun_prop
      exact hi.div hs (hp istar).ne'
    have hratioEv : ∀ᶠ s in 𝓝 lambda, ratio s < rho :=
      hratioCont.eventually_lt_const hratioRho
    let B : ℝ := |(effectiveVelocity L lambda i -
      effectiveVelocity L lambda istar) ^ m| + 1
    have hBpos : 0 < B := by
      dsimp only [B]
      positivity
    have hvelCont : ContinuousAt (fun s =>
        (effectiveVelocity L s i - effectiveVelocity L s istar) ^ m) lambda :=
      ((hasDerivAt_effectiveVelocity L hp i).continuousAt.sub
        (hasDerivAt_effectiveVelocity L hp istar).continuousAt).pow m
    have hvelEv : ∀ᶠ s in 𝓝 lambda,
        |(effectiveVelocity L s i - effectiveVelocity L s istar) ^ m| < B :=
      hvelCont.abs.eventually_lt_const (by
        dsimp only [B]
        linarith)
    have hratioPair : ∀ᶠ p : Param × ℝ in
        𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda), ratio p.2 < rho :=
      by
        have hev : ∀ᶠ p : Param × ℝ in 𝓝 ((⊤ : Param), lambda),
            ratio p.2 < rho :=
          (show ContinuousAt (fun p : Param × ℝ => p.2) (⊤, lambda) from
            continuousAt_snd) hratioEv
        exact hev.filter_mono inf_le_left
    have hvelPair : ∀ᶠ p : Param × ℝ in
        𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda),
        |(effectiveVelocity L p.2 i - effectiveVelocity L p.2 istar) ^ m| < B :=
      by
        have hev : ∀ᶠ p : Param × ℝ in 𝓝 ((⊤ : Param), lambda),
            |(effectiveVelocity L p.2 i - effectiveVelocity L p.2 istar) ^ m| < B :=
          (show ContinuousAt (fun p : Param × ℝ => p.2) (⊤, lambda) from
            continuousAt_snd) hvelEv
        exact hev.filter_mono inf_le_left
    have honeNhds : Ioi (1 : Param) ∈ 𝓝 (⊤ : Param) := by
      rw [nhds_top_basis.mem_iff]
      exact ⟨1, lt_top_iff_ne_top.mpr (by norm_num), Subset.rfl⟩
    have honePair : ∀ᶠ p : Param × ℝ in
        𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda), (1 : Param) < p.1 := by
      have hfst : ContinuousAt (fun p : Param × ℝ => p.1) (⊤, lambda) :=
        continuousAt_fst
      have hev : ∀ᶠ p : Param × ℝ in 𝓝 ((⊤ : Param), lambda),
          (1 : Param) < p.1 := hfst honeNhds
      exact hev.filter_mono inf_le_left
    have hmemK : ∀ᶠ p : Param × ℝ in
        𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda), p.2 ∈ K := by
      filter_upwards [self_mem_nhdsWithin] with p hpK
      exact hpK.2
    have hdecay : Tendsto (fun p : Param × ℝ => B * topRpowDecay rho p.1)
        (𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda)) (𝓝 0) := by
      have ht := (continuousAt_topRpowDecay_top hrho0 hrho1).comp
        (x := ((⊤ : Param), lambda))
        (show ContinuousAt (fun p : Param × ℝ => p.1) (⊤, lambda) from
          continuousAt_fst)
      have htw : Tendsto (fun p : Param × ℝ => topRpowDecay rho p.1)
          (𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda)) (𝓝 0) :=
        by
          have htn : Tendsto (topRpowDecay rho ∘ fun p : Param × ℝ => p.1)
              (𝓝 ((⊤ : Param), lambda))
              (𝓝 ((topRpowDecay rho ∘ fun p : Param × ℝ => p.1) (⊤, lambda))) := ht
          have htn0 : Tendsto (topRpowDecay rho ∘ fun p : Param × ℝ => p.1)
              (𝓝 ((⊤ : Param), lambda)) (𝓝 0) := by
            simpa only [Function.comp_apply, topRpowDecay_top] using htn
          exact htn0.mono_left inf_le_left
      simpa using tendsto_const_nhds.mul htw
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun p : Param × ℝ => B * topRpowDecay rho p.1)
    · exact Eventually.of_forall fun p => norm_nonneg _
    · filter_upwards [hratioPair, hvelPair, honePair, hmemK] with p hratio
        hvel hone hpK
      by_cases htop : p.1 = ⊤
      · simp [topEscortMomentTerm, htop]
      · have hposp := (hfixed p.2 hpK).1
        have hrnonneg : 0 ≤ ENNReal.toReal p.1 := ENNReal.toReal_nonneg
        have hrone : 1 ≤ ENNReal.toReal p.1 := by
          have hone' : finiteParam 1 < p.1 := by simpa using hone
          exact (ENNReal.ofReal_lt_iff_lt_toReal zero_le_one htop).mp hone' |>.le
        have hratio0p : 0 ≤ ratio p.2 :=
          (div_pos (hposp i) (hposp istar)).le
        have hw0 : 0 ≤ escortWeight L (ENNReal.toReal p.1) p.2 i := by
          unfold escortWeight
          exact div_nonneg (Real.rpow_nonneg (hposp i).le _)
            (linePowerSum_pos_all L _ hposp).le
        have hwle : escortWeight L (ENNReal.toReal p.1) p.2 i ≤
            rho ^ ENNReal.toReal p.1 :=
          (escortWeight_le_ratio_rpow L hrnonneg hposp i istar).trans
            (Real.rpow_le_rpow hratio0p hratio.le hrnonneg)
        simp only [topEscortMomentTerm, htop, ↓reduceDIte, Real.norm_eq_abs]
        rw [abs_mul, abs_mul]
        have hfactor : |if withOrder then ENNReal.toReal p.1 else 1| ≤
            ENNReal.toReal p.1 := by
          cases withOrder <;> simp [abs_of_nonneg hrnonneg, hrone]
        calc
          |if withOrder then ENNReal.toReal p.1 else 1| *
                |escortWeight L (ENNReal.toReal p.1) p.2 i| *
              |(effectiveVelocity L p.2 i - effectiveVelocity L p.2 istar) ^ m| ≤
              ENNReal.toReal p.1 * (rho ^ ENNReal.toReal p.1) * B := by
            rw [abs_of_nonneg hw0]
            gcongr
          _ = B * topRpowDecay rho p.1 := by
            simp [topRpowDecay, htop]
            ring
    · exact hdecay

/-- Escort weights sum to one at every positive line point and every real
order. -/
theorem sum_escortWeight_eq_one (L : PositiveLineData I) (a : ℝ)
    {lambda : ℝ} (h : LinePositive L lambda) :
    ∑ i, escortWeight L a lambda i = 1 := by
  unfold escortWeight
  rw [← Finset.sum_div]
  change linePowerSum L a lambda / linePowerSum L a lambda = 1
  exact div_self (linePowerSum_pos_all L a h).ne'

/-- The escort mean centered at an arbitrary coordinate is the corresponding
weighted centered first moment. -/
theorem escortMean_sub_effectiveVelocity_eq_sum (L : PositiveLineData I)
    (a : ℝ) {lambda : ℝ} (h : LinePositive L lambda) (istar : I) :
    escortMean L a lambda - effectiveVelocity L lambda istar =
      ∑ i, escortWeight L a lambda i *
        (effectiveVelocity L lambda i - effectiveVelocity L lambda istar) := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_escortWeight_eq_one L a h, one_mul]
  rfl

/-- Variance expressed around an arbitrary fixed coordinate. -/
theorem escortVar_eq_centered_sum_sub (L : PositiveLineData I)
    (a : ℝ) {lambda : ℝ} (h : LinePositive L lambda) (istar : I) :
    escortVar L a lambda =
      (∑ i, escortWeight L a lambda i *
        (effectiveVelocity L lambda i - effectiveVelocity L lambda istar) ^ 2) -
      (escortMean L a lambda - effectiveVelocity L lambda istar) ^ 2 := by
  have hw := sum_escortWeight_eq_one L a h
  have hcenter :
      (∑ i, escortWeight L a lambda i *
        (effectiveVelocity L lambda i - effectiveVelocity L lambda istar) ^ 2) =
      (∑ i, escortWeight L a lambda i * (effectiveVelocity L lambda i) ^ 2) -
        2 * effectiveVelocity L lambda istar *
          (∑ i, escortWeight L a lambda i * effectiveVelocity L lambda i) +
        (effectiveVelocity L lambda istar) ^ 2 := by
    calc
      (∑ i, escortWeight L a lambda i *
          (effectiveVelocity L lambda i - effectiveVelocity L lambda istar) ^ 2) =
          ∑ i, (escortWeight L a lambda i * (effectiveVelocity L lambda i) ^ 2 -
            2 * effectiveVelocity L lambda istar *
              (escortWeight L a lambda i * effectiveVelocity L lambda i) +
            (effectiveVelocity L lambda istar) ^ 2 * escortWeight L a lambda i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = (∑ i, escortWeight L a lambda i * (effectiveVelocity L lambda i) ^ 2) -
          2 * effectiveVelocity L lambda istar *
            (∑ i, escortWeight L a lambda i * effectiveVelocity L lambda i) +
          (effectiveVelocity L lambda istar) ^ 2 *
            (∑ i, escortWeight L a lambda i) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by rw [hw, mul_one]
  rw [hcenter]
  unfold escortVar escortSecond escortMean
  ring

/-- Escort mean with its fixed-max upper-endpoint value. -/
def fixedMaxEscortMean (L : PositiveLineData I) (istar : I)
    (p : Param × ℝ) : ℝ :=
  if _htop : p.1 = ⊤ then effectiveVelocity L p.2 istar
  else escortMean L (ENNReal.toReal p.1) p.2

/-- The order-weighted escort variance, extended by zero at the upper
endpoint. -/
def fixedMaxOrderEscortVar (L : PositiveLineData I) (p : Param × ℝ) : ℝ :=
  if _htop : p.1 = ⊤ then 0
  else ENNReal.toReal p.1 * escortVar L (ENNReal.toReal p.1) p.2

omit [Nonempty I] in
@[simp] theorem fixedMaxEscortMean_top (L : PositiveLineData I)
    (istar : I) (lambda : ℝ) :
    fixedMaxEscortMean L istar (⊤, lambda) = effectiveVelocity L lambda istar := by
  simp [fixedMaxEscortMean]

omit [Nonempty I] in
@[simp] theorem fixedMaxOrderEscortVar_top (L : PositiveLineData I)
    (lambda : ℝ) : fixedMaxOrderEscortVar L (⊤, lambda) = 0 := by
  simp [fixedMaxOrderEscortVar]

/-- Uniform fixed-max escort concentration, jointly in order and line
parameter. -/
theorem continuousWithinAt_fixedMaxEscortMean_top
    (L : PositiveLineData I) {K : Set ℝ} {istar : I}
    (hfixed : FixedMaxCoordinate L K istar)
    {lambda : ℝ} (hlambda : lambda ∈ K) :
    ContinuousWithinAt (fixedMaxEscortMean L istar)
      (Set.univ ×ˢ K) ((⊤ : Param), lambda) := by
  change Tendsto (fixedMaxEscortMean L istar)
    (𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda))
    (𝓝 (effectiveVelocity L lambda istar))
  have hterms : Tendsto (fun p : Param × ℝ =>
      ∑ i, topEscortMomentTerm L istar i false 1 p)
      (𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda)) (𝓝 0) :=
    by
      simpa using tendsto_finsetSum Finset.univ fun i _hi =>
        tendsto_topEscortMomentTerm_fixedMax L (i := i) hfixed hlambda
          zero_lt_one false
  have hstar : Tendsto (fun p : Param × ℝ => effectiveVelocity L p.2 istar)
      (𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda))
      (𝓝 (effectiveVelocity L lambda istar)) := by
    have hc : ContinuousAt (fun p : Param × ℝ =>
        effectiveVelocity L p.2 istar) (⊤, lambda) := by
      have hv := (hasDerivAt_effectiveVelocity L
        (hfixed lambda hlambda).1 istar).continuousAt
      have hsnd : ContinuousAt (fun p : Param × ℝ => p.2) (⊤, lambda) :=
        continuousAt_snd
      change ContinuousAt ((fun s => effectiveVelocity L s istar) ∘
        fun p : Param × ℝ => p.2) (⊤, lambda)
      exact hv.comp (x := ((⊤ : Param), lambda)) hsnd
    exact hc.continuousWithinAt
  have hsum := hterms.add hstar
  have heq : fixedMaxEscortMean L istar =ᶠ[
      𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda)] fun p =>
        (∑ i, topEscortMomentTerm L istar i false 1 p) +
          effectiveVelocity L p.2 istar := by
    filter_upwards [self_mem_nhdsWithin] with p hpK
    by_cases htop : p.1 = ⊤
    · simp [fixedMaxEscortMean, topEscortMomentTerm, htop]
    · have hp := (hfixed p.2 hpK.2).1
      rw [fixedMaxEscortMean, dif_neg htop]
      have hterm (i : I) : topEscortMomentTerm L istar i false 1 p =
          escortWeight L (ENNReal.toReal p.1) p.2 i *
            (effectiveVelocity L p.2 i - effectiveVelocity L p.2 istar) := by
        rw [topEscortMomentTerm, dif_neg htop]
        simp
      simp_rw [hterm]
      rw [← escortMean_sub_effectiveVelocity_eq_sum L
        (ENNReal.toReal p.1) hp istar]
      ring
  simpa only [zero_add] using hsum.congr' heq.symm

/-- The uniform concentration rate needed by the second derivative:
`alpha * escortVar` tends jointly to zero at the fixed-max endpoint. -/
theorem continuousWithinAt_fixedMaxOrderEscortVar_top
    (L : PositiveLineData I) {K : Set ℝ} {istar : I}
    (hfixed : FixedMaxCoordinate L K istar)
    {lambda : ℝ} (hlambda : lambda ∈ K) :
    ContinuousWithinAt (fixedMaxOrderEscortVar L)
      (Set.univ ×ˢ K) ((⊤ : Param), lambda) := by
  change Tendsto (fixedMaxOrderEscortVar L)
    (𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda)) (𝓝 0)
  let S0 : Param × ℝ → ℝ := fun p =>
    ∑ i, topEscortMomentTerm L istar i false 1 p
  let S1 : Param × ℝ → ℝ := fun p =>
    ∑ i, topEscortMomentTerm L istar i true 1 p
  let S2 : Param × ℝ → ℝ := fun p =>
    ∑ i, topEscortMomentTerm L istar i true 2 p
  have hS0 : Tendsto S0
      (𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda)) (𝓝 0) :=
    by
      simpa [S0] using tendsto_finsetSum Finset.univ fun i _hi =>
        tendsto_topEscortMomentTerm_fixedMax L (i := i) hfixed hlambda
          zero_lt_one false
  have hS1 : Tendsto S1
      (𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda)) (𝓝 0) :=
    by
      simpa [S1] using tendsto_finsetSum Finset.univ fun i _hi =>
        tendsto_topEscortMomentTerm_fixedMax L (i := i) hfixed hlambda
          zero_lt_one true
  have hS2 : Tendsto S2
      (𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda)) (𝓝 0) :=
    by
      simpa [S2] using tendsto_finsetSum Finset.univ fun i _hi =>
        tendsto_topEscortMomentTerm_fixedMax L (i := i) hfixed hlambda
          (by norm_num) true
  have hcomb : Tendsto (fun p => S2 p - S1 p * S0 p)
      (𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda)) (𝓝 0) := by
    simpa using hS2.sub (hS1.mul hS0)
  have heq : fixedMaxOrderEscortVar L =ᶠ[
      𝓝[Set.univ ×ˢ K] ((⊤ : Param), lambda)] fun p =>
        S2 p - S1 p * S0 p := by
    filter_upwards [self_mem_nhdsWithin] with p hpK
    by_cases htop : p.1 = ⊤
    · simp [fixedMaxOrderEscortVar, topEscortMomentTerm, S0, S1, S2, htop]
    · have hp := (hfixed p.2 hpK.2).1
      rw [fixedMaxOrderEscortVar, dif_neg htop]
      dsimp only [S0, S1, S2]
      have hterm0 (i : I) : topEscortMomentTerm L istar i false 1 p =
          escortWeight L (ENNReal.toReal p.1) p.2 i *
            (effectiveVelocity L p.2 i - effectiveVelocity L p.2 istar) := by
        rw [topEscortMomentTerm, dif_neg htop]
        simp
      have hterm1 (i : I) : topEscortMomentTerm L istar i true 1 p =
          ENNReal.toReal p.1 * escortWeight L (ENNReal.toReal p.1) p.2 i *
            (effectiveVelocity L p.2 i - effectiveVelocity L p.2 istar) := by
        rw [topEscortMomentTerm, dif_neg htop]
        simp
      have hterm2 (i : I) : topEscortMomentTerm L istar i true 2 p =
          ENNReal.toReal p.1 * escortWeight L (ENNReal.toReal p.1) p.2 i *
            (effectiveVelocity L p.2 i - effectiveVelocity L p.2 istar) ^ 2 := by
        rw [topEscortMomentTerm, dif_neg htop]
        simp
      simp_rw [hterm0, hterm1, hterm2]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [escortVar_eq_centered_sum_sub L (ENNReal.toReal p.1) hp istar]
      rw [escortMean_sub_effectiveVelocity_eq_sum L
        (ENNReal.toReal p.1) hp istar]
      ring
  exact hcomb.congr' heq.symm

omit [Fintype I] [Nonempty I] in
/-- A fixed maximum on a compact interval extends to an open fixed-max
neighborhood of each interval point.  Tied affine coordinates are rigid;
all other inequalities are locally strict. -/
theorem exists_open_fixedMax_neighborhood
    [Finite I] (L : PositiveLineData I) {K : Set ℝ} {istar : I}
    (hfixed : FixedMaxCoordinate L K istar)
    {lambda : ℝ} (hlambda : lambda ∈ K) :
    ∃ U : Set ℝ, IsOpen U ∧ lambda ∈ U ∧
      FixedMaxCoordinate L U istar := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  have hp := (hfixed lambda hlambda).1
  let P : I → ℝ → Prop := fun i s =>
    lineRaw L s i ≤ lineRaw L s istar ∧
      (LinePositive L s → lineRaw L s i = lineRaw L s istar →
        effectiveVelocity L s i = effectiveVelocity L s istar)
  have hcoord (i : I) : ∀ᶠ s in 𝓝 lambda, P i s := by
    by_cases htie : lineRaw L lambda i = lineRaw L lambda istar
    · filter_upwards [] with s
      have hraw := fixedMax_tie_lineRaw_eq L hfixed hlambda htie s
      refine ⟨hraw.le, fun hs _heq => ?_⟩
      exact fixedMax_tie_effectiveVelocity_eq L hfixed hlambda htie hs
    · have hlt : lineRaw L lambda i < lineRaw L lambda istar :=
        lt_of_le_of_ne ((hfixed lambda hlambda).2.1 i) htie
      have hc : ContinuousAt (fun s =>
          lineRaw L s i - lineRaw L s istar) lambda := by
        unfold lineRaw
        fun_prop
      have hev : ∀ᶠ s in 𝓝 lambda,
          lineRaw L s i - lineRaw L s istar < 0 :=
        hc.eventually_lt_const (by linarith)
      filter_upwards [hev] with s hs
      have hstrict : lineRaw L s i < lineRaw L s istar := by linarith
      exact ⟨hstrict.le, fun _hpos heq => (ne_of_lt hstrict heq).elim⟩
  have hallFinset : ∀ t : Finset I, ∀ᶠ s in 𝓝 lambda,
      ∀ i ∈ t, P i s := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hit iht =>
        filter_upwards [hcoord i, iht] with s hi hs
        intro j hj
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact hi
        · exact hs j hj
  have hall : ∀ᶠ s in 𝓝 lambda, ∀ i, P i s := by
    have hu := hallFinset Finset.univ
    filter_upwards [hu] with s hs
    exact fun i => hs i (Finset.mem_univ i)
  have hposEv : ∀ᶠ s in 𝓝 lambda, LinePositive L s :=
    isOpen_setOf_linePositive L |>.mem_nhds hp
  have hprop : ∀ᶠ s in 𝓝 lambda,
      LinePositive L s ∧
        (∀ i, lineRaw L s i ≤ lineRaw L s istar) ∧
        (∀ i, lineRaw L s i = lineRaw L s istar →
          effectiveVelocity L s i = effectiveVelocity L s istar) := by
    filter_upwards [hposEv, hall] with s hspos hs
    exact ⟨hspos, fun i => (hs i).1, fun i hi => (hs i).2 hspos hi⟩
  rcases mem_nhds_iff.mp hprop with ⟨U, hUsub, hUopen, hlambdaU⟩
  exact ⟨U, hUopen, hlambdaU, fun s hs => hUsub hs⟩

/-! ### A uniform finite-order estimate at min-entropy -/

/-- Above order one, finite Rényi entropy differs from min-entropy by at most
`log(card I) / (a - 1)`.  The estimate is uniform in the probability vector;
this is the compactness-free input for joint upper-endpoint continuity. -/
theorem abs_renyiFinite_sub_renyiTop_le (p : ProbVec I) {a : ℝ}
    (ha : 1 < a) :
    |renyiFinite a p - renyiTop p| ≤
      Real.log (Fintype.card I : ℝ) / (a - 1) := by
  let m : ℝ := finMax p.1
  let n : ℝ := Fintype.card I
  have hmpos : 0 < m := finMax_pos p
  have hmle : m ≤ 1 := finMax_le_one p
  have hnpos : 0 < n := by
    dsimp only [n]
    exact_mod_cast Fintype.card_pos
  have hapos : 0 < a := zero_lt_one.trans ha
  have hpowpos : 0 < powerSum a p := powerSum_pos hapos p
  have hpowlower : m ^ a ≤ powerSum a p := by
    obtain ⟨i, hi⟩ := finMax_mem p.1
    rw [powerSum]
    calc
      m ^ a = p.1 i ^ a := by rw [hi]
      _ ≤ ∑ j, p.1 j ^ a :=
        Finset.single_le_sum
          (fun j _hj => Real.rpow_nonneg (p.2.1 j) a)
          (Finset.mem_univ i)
  have hpowupper : powerSum a p ≤ n * m ^ a := by
    rw [powerSum]
    calc
      (∑ i, p.1 i ^ a) ≤ ∑ _i : I, m ^ a := by
        apply Finset.sum_le_sum
        intro i _hi
        exact Real.rpow_le_rpow (p.2.1 i) (le_finMax p i) hapos.le
      _ = n * m ^ a := by simp [n, nsmul_eq_mul]
  have hloglower : a * Real.log m ≤ Real.log (powerSum a p) := by
    have h := Real.strictMonoOn_log.monotoneOn
      (Real.rpow_pos_of_pos hmpos a) hpowpos hpowlower
    simpa [Real.log_rpow hmpos] using h
  have hupperpos : 0 < n * m ^ a :=
    mul_pos hnpos (Real.rpow_pos_of_pos hmpos a)
  have hlogupper : Real.log (powerSum a p) ≤
      Real.log n + a * Real.log m := by
    have h := Real.strictMonoOn_log.monotoneOn hpowpos hupperpos hpowupper
    rw [Real.log_mul hnpos.ne' (Real.rpow_pos_of_pos hmpos a).ne',
      Real.log_rpow hmpos] at h
    exact h
  have hlogm : Real.log m ≤ 0 := Real.log_nonpos hmpos.le hmle
  have htopBound : -Real.log m ≤ Real.log n := by
    simpa [renyiTop, m, n] using renyiTop_le_log_card p
  let q : ℝ := -Real.log (powerSum a p) + (a - 1) * Real.log m
  have hqlower : -Real.log n ≤ q := by
    dsimp only [q]
    linarith
  have hqupper : q ≤ Real.log n := by
    dsimp only [q]
    linarith
  have hqabs : |q| ≤ Real.log n := abs_le.mpr ⟨hqlower, hqupper⟩
  have hdenpos : 0 < a - 1 := sub_pos.mpr ha
  have hdiff : renyiFinite a p - renyiTop p = q / (a - 1) := by
    dsimp only [q, m]
    unfold renyiFinite renyiTop
    have hdenne : 1 - a ≠ 0 := by linarith
    field_simp [hdenpos.ne', hdenne]
    ring
  rw [hdiff, abs_div, abs_of_pos hdenpos]
  exact div_le_div_of_nonneg_right hqabs hdenpos.le

/-- The entropy itself is jointly continuous at the compactified upper
endpoint.  The finite-alphabet estimate is uniform in the probability
vector, while the fixed-max hypothesis supplies continuity of the limiting
min-entropy line in the line parameter. -/
theorem continuousWithinAt_entropyLine_top
    (L : PositiveLineData I) {K : Set ℝ} {istar : I}
    (hfixed : FixedMaxCoordinate L K istar)
    {lambda : ℝ} (hlambda : lambda ∈ K) :
    ContinuousWithinAt (fun p : Param × ℝ => entropyLine L p.1 p.2)
      (Set.univ ×ˢ K) ((⊤ : Param), lambda) := by
  let D : Set (Param × ℝ) := Set.univ ×ˢ K
  let x : Param × ℝ := ((⊤ : Param), lambda)
  change Tendsto (fun p : Param × ℝ => entropyLine L p.1 p.2)
    (𝓝[D] x) (𝓝 (entropyLine L ⊤ lambda))
  let c : ℝ := Real.log (Fintype.card I : ℝ)
  let b : Param → ℝ := compactifyZeroAtTop (fun r : ℝ => c / (r - 1))
  have hden : Tendsto (fun r : ℝ => r - 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro q
    refine ⟨q + 1, ?_⟩
    intro r hr
    linarith
  have hreal : Tendsto (fun r : ℝ => c / (r - 1)) atTop (𝓝 0) :=
    hden.const_div_atTop c
  have hbAt : ContinuousAt b (⊤ : Param) := by
    exact continuousAt_compactifyZeroAtTop (fun r : ℝ => c / (r - 1)) hreal
  have hb : Tendsto (fun p : Param × ℝ => b p.1)
      (𝓝[D] x) (𝓝 0) := by
    have hcomp : ContinuousAt (b ∘ fun p : Param × ℝ => p.1) x :=
      hbAt.comp (x := x) continuousAt_fst
    exact hcomp.continuousWithinAt
  have htopOrder : Ioi (1 : Param) ∈ 𝓝 (⊤ : Param) := by
    rw [nhds_top_basis.mem_iff]
    exact ⟨1, lt_top_iff_ne_top.mpr (by norm_num), Subset.rfl⟩
  have horderEvent : ∀ᶠ p : Param × ℝ in 𝓝[D] x, (1 : Param) < p.1 := by
    have hfst : ContinuousAt (fun p : Param × ℝ => p.1) x := continuousAt_fst
    have hfull : ∀ᶠ p : Param × ℝ in 𝓝 x, (1 : Param) < p.1 :=
      hfst htopOrder
    exact hfull.filter_mono inf_le_left
  have herr : Tendsto (fun p : Param × ℝ =>
      entropyLine L p.1 p.2 - entropyLine L ⊤ p.2)
      (𝓝[D] x) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun p : Param × ℝ => b p.1)
    · exact Eventually.of_forall fun p => norm_nonneg _
    · filter_upwards [horderEvent] with p hporder
      by_cases htop : p.1 = ⊤
      · simp [b, compactifyZeroAtTop, htop]
      · let r : ℝ := ENNReal.toReal p.1
        have hrgt : 1 < r := by
          have hporder' : finiteParam 1 < p.1 := by simpa using hporder
          exact (ENNReal.ofReal_lt_iff_lt_toReal zero_le_one htop).mp hporder'
        have hrpos : 0 < r := zero_lt_one.trans hrgt
        have hrone : r ≠ 1 := ne_of_gt hrgt
        have hreconstruct : finiteParam r = p.1 := ENNReal.ofReal_toReal htop
        have hbound := abs_renyiFinite_sub_renyiTop_le
          (lineProb L p.2) hrgt
        have hfinite : entropyLine L p.1 p.2 =
            renyiFinite r (lineProb L p.2) := by
          rw [← hreconstruct]
          exact renyi_finite hrpos.le hrpos.ne' hrone (lineProb L p.2)
        have htopValue : entropyLine L ⊤ p.2 =
            renyiTop (lineProb L p.2) := by
          exact renyi_at_top (lineProb L p.2)
        rw [hfinite, htopValue]
        simpa [b, compactifyZeroAtTop, htop, c, r] using hbound
    · exact hb
  rcases exists_open_fixedMax_neighborhood L hfixed hlambda with
    ⟨U, hUopen, hlambdaU, hfixedU⟩
  have htopLineAt : ContinuousAt (entropyLine L ⊤) lambda :=
    (hasDerivAt_entropyLine_top_on L hUopen hfixedU hlambdaU).continuousAt
  have htopLine : Tendsto (fun p : Param × ℝ => entropyLine L ⊤ p.2)
      (𝓝[D] x) (𝓝 (entropyLine L ⊤ lambda)) := by
    have hcomp : ContinuousAt
        ((entropyLine L ⊤) ∘ fun p : Param × ℝ => p.2) x :=
      htopLineAt.comp (x := x) continuousAt_snd
    exact hcomp.continuousWithinAt
  have hsum := herr.add htopLine
  simpa only [sub_add_cancel, zero_add, D, x] using hsum

/-! ### Joint upper-endpoint continuity of the line derivatives -/

/-- A formula extending the finite-order first derivative continuously across
the fixed-max upper endpoint. -/
def fixedMaxFirstSurrogate (L : PositiveLineData I) (istar : I)
    (p : Param × ℝ) : ℝ :=
  singularWeight p.1 *
    (fixedMaxEscortMean L istar p - escortMean L 1 p.2)

/-- A formula extending the finite-order second derivative continuously across
the fixed-max upper endpoint. -/
def fixedMaxSecondSurrogate (L : PositiveLineData I) (istar : I)
    (p : Param × ℝ) : ℝ :=
  -fixedMaxOrderEscortVar L p + singularWeight p.1 *
    ((escortMean L 1 p.2) ^ 2 - (fixedMaxEscortMean L istar p) ^ 2)

/-- At a fixed maximal coordinate, both entropy-line derivatives are jointly
continuous at the compactified upper endpoint. -/
theorem continuousWithinAt_entropyLine_derivatives_top
    (L : PositiveLineData I) {K : Set ℝ} {istar : I}
    (hfixed : FixedMaxCoordinate L K istar)
    {lambda : ℝ} (hlambda : lambda ∈ K) :
    ContinuousWithinAt (fun p : Param × ℝ => entropyLineFirst L p.1 p.2)
        (Set.univ ×ˢ K) ((⊤ : Param), lambda) ∧
      ContinuousWithinAt (fun p : Param × ℝ => entropyLineSecond L p.1 p.2)
        (Set.univ ×ˢ K) ((⊤ : Param), lambda) := by
  let D : Set (Param × ℝ) := Set.univ ×ˢ K
  let x : Param × ℝ := ((⊤ : Param), lambda)
  have hp := (hfixed lambda hlambda).1
  have hsingAt : ContinuousAt (fun p : Param × ℝ => singularWeight p.1) x := by
    change ContinuousAt (singularWeight ∘ fun p : Param × ℝ => p.1) x
    exact continuousAt_singularWeight_top.comp (x := x) continuousAt_fst
  have hsing : ContinuousWithinAt (fun p : Param × ℝ => singularWeight p.1)
      D x := hsingAt.continuousWithinAt
  have hmeanAt : ContinuousAt (fun p : Param × ℝ => escortMean L 1 p.2) x := by
    change ContinuousAt (escortMean L 1 ∘ fun p : Param × ℝ => p.2) x
    exact (hasDerivAt_escortMean L zero_lt_one hp).continuousAt.comp
      (x := x) continuousAt_snd
  have hmean : ContinuousWithinAt
      (fun p : Param × ℝ => escortMean L 1 p.2) D x :=
    hmeanAt.continuousWithinAt
  have hfixedMean := continuousWithinAt_fixedMaxEscortMean_top L hfixed hlambda
  have hfixedVar := continuousWithinAt_fixedMaxOrderEscortVar_top L hfixed hlambda
  have hfirstSurrogate : ContinuousWithinAt
      (fixedMaxFirstSurrogate L istar) D x := by
    unfold fixedMaxFirstSurrogate
    exact hsing.mul (hfixedMean.sub hmean)
  have hsecondSurrogate : ContinuousWithinAt
      (fixedMaxSecondSurrogate L istar) D x := by
    unfold fixedMaxSecondSurrogate
    exact hfixedVar.neg.add
      (hsing.mul ((hmean.pow 2).sub (hfixedMean.pow 2)))
  rcases exists_open_fixedMax_neighborhood L hfixed hlambda with
    ⟨U, hUopen, hlambdaU, hfixedU⟩
  have hUevent : ∀ᶠ p : Param × ℝ in 𝓝[D] x, p.2 ∈ U := by
    have hfull : ∀ᶠ p : Param × ℝ in 𝓝 x, p.2 ∈ U :=
      continuousAt_snd (hUopen.mem_nhds hlambdaU)
    exact hfull.filter_mono inf_le_left
  have htopOrder : Ioi (1 : Param) ∈ 𝓝 (⊤ : Param) := by
    rw [nhds_top_basis.mem_iff]
    exact ⟨1, lt_top_iff_ne_top.mpr (by norm_num), Subset.rfl⟩
  have horderEvent : ∀ᶠ p : Param × ℝ in 𝓝[D] x, (1 : Param) < p.1 := by
    have hfst : ContinuousAt (fun p : Param × ℝ => p.1) x := continuousAt_fst
    have hfull : ∀ᶠ p : Param × ℝ in 𝓝 x, (1 : Param) < p.1 :=
      hfst htopOrder
    exact hfull.filter_mono inf_le_left
  have hfirstEq : (fun p : Param × ℝ => entropyLineFirst L p.1 p.2) =ᶠ[
      𝓝[D] x] fixedMaxFirstSurrogate L istar := by
    filter_upwards [hUevent, horderEvent] with p hpU hporder
    by_cases htop : p.1 = ⊤
    · rw [htop]
      rw [entropyLineFirst_top_on L hUopen hfixedU hpU]
      rw [fixedMaxFirstSurrogate, fixedMaxEscortMean, dif_pos htop]
      have hsing : singularWeight p.1 = -1 := by
        rw [htop]
        exact singularWeight_top
      rw [hsing]
      ring
    · let r : ℝ := ENNReal.toReal p.1
      have hrgt : 1 < r := by
        have hporder' : finiteParam 1 < p.1 := by simpa using hporder
        exact (ENNReal.ofReal_lt_iff_lt_toReal zero_le_one htop).mp hporder'
      have hrpos : 0 < r := zero_lt_one.trans hrgt
      have hrone : r ≠ 1 := ne_of_gt hrgt
      have hreconstruct : finiteParam r = p.1 := ENNReal.ofReal_toReal htop
      calc
        entropyLineFirst L p.1 p.2 =
            entropyLineFirst L (finiteParam r) p.2 := by rw [hreconstruct]
        _ = singularWeight (finiteParam r) *
            (escortMean L r p.2 - escortMean L 1 p.2) :=
          entropyLineFirst_finite_on L hUopen
            (fun s hs => (hfixedU s hs).1) hrpos hrone hpU
        _ = fixedMaxFirstSurrogate L istar p := by
          rw [fixedMaxFirstSurrogate, fixedMaxEscortMean, dif_neg htop,
            hreconstruct]
  have hsecondEq : (fun p : Param × ℝ => entropyLineSecond L p.1 p.2) =ᶠ[
      𝓝[D] x] fixedMaxSecondSurrogate L istar := by
    filter_upwards [hUevent, horderEvent] with p hpU hporder
    by_cases htop : p.1 = ⊤
    · rw [htop]
      rw [entropyLineSecond_top_on L hUopen hfixedU hpU]
      rw [fixedMaxSecondSurrogate, fixedMaxEscortMean, dif_pos htop,
        fixedMaxOrderEscortVar, dif_pos htop]
      have hsing : singularWeight p.1 = -1 := by
        rw [htop]
        exact singularWeight_top
      rw [hsing]
      ring
    · let r : ℝ := ENNReal.toReal p.1
      have hrgt : 1 < r := by
        have hporder' : finiteParam 1 < p.1 := by simpa using hporder
        exact (ENNReal.ofReal_lt_iff_lt_toReal zero_le_one htop).mp hporder'
      have hrpos : 0 < r := zero_lt_one.trans hrgt
      have hrone : r ≠ 1 := ne_of_gt hrgt
      have hreconstruct : finiteParam r = p.1 := ENNReal.ofReal_toReal htop
      calc
        entropyLineSecond L p.1 p.2 =
            entropyLineSecond L (finiteParam r) p.2 := by rw [hreconstruct]
        _ = -r * escortVar L r p.2 + singularWeight (finiteParam r) *
            ((escortMean L 1 p.2) ^ 2 - (escortMean L r p.2) ^ 2) :=
          entropyLineSecond_finite_on L hUopen
            (fun s hs => (hfixedU s hs).1) hrpos hrone hpU
        _ = fixedMaxSecondSurrogate L istar p := by
          rw [fixedMaxSecondSurrogate, fixedMaxEscortMean, dif_neg htop,
            fixedMaxOrderEscortVar, dif_neg htop, hreconstruct]
          dsimp only [r]
          ring
  refine ⟨hfirstSurrogate.congr_of_eventuallyEq hfirstEq ?_,
    hsecondSurrogate.congr_of_eventuallyEq hsecondEq ?_⟩
  · dsimp only [x]
    rw [entropyLineFirst_top_on L hUopen hfixedU hlambdaU]
    simp [fixedMaxFirstSurrogate, fixedMaxEscortMean]
  · dsimp only [x]
    rw [entropyLineSecond_top_on L hUopen hfixedU hlambdaU]
    simp [fixedMaxSecondSurrogate, fixedMaxEscortMean,
      fixedMaxOrderEscortVar]

/-- Joint continuity of entropy and its first two line derivatives on the
full compactified order interval and a fixed positive line interval. -/
theorem continuousOn_entropyLine_full_bundle
    (L : PositiveLineData I) {lambda0 : ℝ} (hlambda0 : 0 < lambda0)
    (hpos : ∀ lambda ∈ Icc (-lambda0) lambda0, LinePositive L lambda)
    {istar : I}
    (hfixed : FixedMaxCoordinate L (Icc (-lambda0) lambda0) istar) :
    ContinuousOn (fun p : Param × ℝ => entropyLine L p.1 p.2)
        (Set.univ ×ˢ Icc (-lambda0) lambda0) ∧
      ContinuousOn (fun p : Param × ℝ => entropyLineFirst L p.1 p.2)
        (Set.univ ×ˢ Icc (-lambda0) lambda0) ∧
      ContinuousOn (fun p : Param × ℝ => entropyLineSecond L p.1 p.2)
        (Set.univ ×ˢ Icc (-lambda0) lambda0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    by_cases htop : p.1 = ⊤
    · have hpEq : p = ((⊤ : Param), p.2) := Prod.ext htop rfl
      rw [hpEq]
      exact continuousWithinAt_entropyLine_top L hfixed hp.2
    · exact (continuousWithinAt_entropyLine_bundle_of_ne_top
        L hlambda0 hpos htop hp.2).1
  · intro p hp
    by_cases htop : p.1 = ⊤
    · have hpEq : p = ((⊤ : Param), p.2) := Prod.ext htop rfl
      rw [hpEq]
      exact (continuousWithinAt_entropyLine_derivatives_top L hfixed hp.2).1
    · exact (continuousWithinAt_entropyLine_bundle_of_ne_top
        L hlambda0 hpos htop hp.2).2.1
  · intro p hp
    by_cases htop : p.1 = ⊤
    · have hpEq : p = ((⊤ : Param), p.2) := Prod.ext htop rfl
      rw [hpEq]
      exact (continuousWithinAt_entropyLine_derivatives_top L hfixed hp.2).2
    · exact (continuousWithinAt_entropyLine_bundle_of_ne_top
        L hlambda0 hpos htop hp.2).2.2

/-- The manuscript's literal exact-derivatives package: finite formulas,
their base-point specialization (including the expanded rational identity),
all three endpoint formulas, and joint continuity on compactified order
space. -/
theorem exactDerivatives (L : PositiveLineData I) {lambda0 : ℝ}
    (hlambda0 : 0 < lambda0)
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
    (∀ a : ℝ, 0 < a → a ≠ 1 →
      entropyLineFirst L (finiteParam a) 0 =
        singularWeight (finiteParam a) *
          (escortMean L a 0 - escortMean L 1 0) ∧
      entropyLineSecond L (finiteParam a) 0 =
        -a * escortVar L a 0 +
          singularWeight (finiteParam a) *
            ((escortMean L 1 0) ^ 2 - (escortMean L a 0) ^ 2) ∧
      entropyLineSecond L (finiteParam a) 0 =
        (a * (a - 1) * escortSecond L a 0 -
            a ^ 2 * (escortMean L a 0) ^ 2 +
          a * (escortMean L 1 0) ^ 2) / (1 - a)) ∧
    (∀ lambda ∈ Ioo (-lambda0) lambda0,
      entropyLineFirst L 0 lambda = 0 ∧
      entropyLineSecond L 0 lambda = 0 ∧
      entropyLineFirst L 1 lambda = shannonLineSlope L lambda ∧
      entropyLineSecond L 1 lambda =
        -escortVar L 1 lambda -
          2 * escortMean L 1 lambda * shannonLineSlope L lambda) ∧
    (∀ istar : I,
      FixedMaxCoordinate L (Icc (-lambda0) lambda0) istar →
      ∀ lambda ∈ Ioo (-lambda0) lambda0,
        entropyLineFirst L ⊤ lambda =
          escortMean L 1 lambda - effectiveVelocity L lambda istar ∧
        entropyLineSecond L ⊤ lambda =
          (effectiveVelocity L lambda istar) ^ 2 -
            (escortMean L 1 lambda) ^ 2) ∧
    (∀ istar : I,
      FixedMaxCoordinate L (Icc (-lambda0) lambda0) istar →
      ContinuousOn (fun p : Param × ℝ => entropyLine L p.1 p.2)
          (Set.univ ×ˢ Icc (-lambda0) lambda0) ∧
        ContinuousOn (fun p : Param × ℝ => entropyLineFirst L p.1 p.2)
          (Set.univ ×ˢ Icc (-lambda0) lambda0) ∧
        ContinuousOn (fun p : Param × ℝ => entropyLineSecond L p.1 p.2)
          (Set.univ ×ˢ Icc (-lambda0) lambda0)) := by
  rcases exactEntropyDerivativeFormulas L hlambda0 hpos with
    ⟨hfinite, hendpoint, htop⟩
  refine ⟨hfinite, ?_, hendpoint, htop, ?_⟩
  · intro a ha ha1
    exact ⟨entropyLineFirst_finite_zero L ha ha1,
      entropyLineSecond_finite_zero L ha ha1,
      entropyLineSecond_finite_zero_expanded L ha ha1⟩
  · intro istar hfixed
    exact continuousOn_entropyLine_full_bundle L hlambda0 hpos hfixed

end ClippedFiniteParameter

end ConditionalEntropy
