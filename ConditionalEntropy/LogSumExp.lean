import ConditionalEntropy.FiniteExtrema
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Finite log-sum-exp

Exact finite-temperature bounds and all three tropical/derivation limits for
a strictly positive finite probability family.
-/

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace ConditionalEntropy

universe u

def weightedExpSum {J : Type u} [Fintype J]
    (p a : J → ℝ) (t : ℝ) : ℝ :=
  ∑ j, p j * Real.exp (t * a j)

def logSumExp {J : Type u} [Fintype J]
    (p a : J → ℝ) (t : ℝ) : ℝ :=
  Real.log (weightedExpSum p a t) / t

theorem weightedExpSum_pos {J : Type u} [Fintype J] [Nonempty J]
    (p a : J → ℝ) (hp : ∀ j, 0 < p j) (t : ℝ) :
    0 < weightedExpSum p a t := by
  classical
  unfold weightedExpSum
  apply Finset.sum_pos'
  · intro j _
    exact (mul_pos (hp j) (Real.exp_pos _)).le
  · let j : J := Classical.choice inferInstance
    exact ⟨j, Finset.mem_univ j, mul_pos (hp j) (Real.exp_pos _)⟩

@[simp] theorem weightedExpSum_zero {J : Type u} [Fintype J]
    (p a : J → ℝ) (hsum : ∑ j, p j = 1) :
    weightedExpSum p a 0 = 1 := by
  simp [weightedExpSum, hsum]

theorem weightedExpSum_le_min_exp {J : Type u} [Fintype J] [Nonempty J]
    (p a : J → ℝ) (hp : ∀ j, 0 < p j) (hsum : ∑ j, p j = 1)
    {t : ℝ} (ht : t < 0) :
    weightedExpSum p a t ≤ Real.exp (t * finMin a) := by
  calc
    weightedExpSum p a t ≤ ∑ j, p j * Real.exp (t * finMin a) := by
      unfold weightedExpSum
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hp j).le
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (finMin_le a j) ht.le)
    _ = Real.exp (t * finMin a) := by
      rw [← Finset.sum_mul, hsum, one_mul]

theorem max_exp_le_weightedExpSum {J : Type u} [Fintype J] [Nonempty J]
    (p a : J → ℝ) (hp : ∀ j, 0 < p j) (hsum : ∑ j, p j = 1)
    {t : ℝ} (ht : 0 < t) :
    weightedExpSum p a t ≤ Real.exp (t * finMax a) := by
  calc
    weightedExpSum p a t ≤ ∑ j, p j * Real.exp (t * finMax a) := by
      unfold weightedExpSum
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hp j).le
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (le_finMax_apply a j) ht.le)
    _ = Real.exp (t * finMax a) := by
      rw [← Finset.sum_mul, hsum, one_mul]

theorem min_witness_exp_le {J : Type u} [Fintype J] [Nonempty J]
    (p a : J → ℝ) (hp : ∀ j, 0 < p j) (jmin : J)
    (hjmin : a jmin = finMin a) (t : ℝ) :
    p jmin * Real.exp (t * finMin a) ≤ weightedExpSum p a t := by
  unfold weightedExpSum
  have hterm : p jmin * Real.exp (t * finMin a) =
      p jmin * Real.exp (t * a jmin) := by rw [hjmin]
  rw [hterm]
  exact Finset.single_le_sum
    (fun j _ => (mul_pos (hp j) (Real.exp_pos (t * a j))).le)
    (Finset.mem_univ jmin)

theorem max_witness_exp_le {J : Type u} [Fintype J] [Nonempty J]
    (p a : J → ℝ) (hp : ∀ j, 0 < p j) (jmax : J)
    (hjmax : a jmax = finMax a) (t : ℝ) :
    p jmax * Real.exp (t * finMax a) ≤ weightedExpSum p a t := by
  unfold weightedExpSum
  have hterm : p jmax * Real.exp (t * finMax a) =
      p jmax * Real.exp (t * a jmax) := by rw [hjmax]
  rw [hterm]
  exact Finset.single_le_sum
    (fun j _ => (mul_pos (hp j) (Real.exp_pos (t * a j))).le)
    (Finset.mem_univ jmax)

/-- Negative-temperature sharp two-sided bound. -/
theorem logSumExp_bounds_neg {J : Type u} [Fintype J] [Nonempty J]
    (p a : J → ℝ) (hp : ∀ j, 0 < p j) (hsum : ∑ j, p j = 1)
    (jmin : J) (hjmin : a jmin = finMin a) {t : ℝ} (ht : t < 0) :
    finMin a ≤ logSumExp p a t ∧
      logSumExp p a t ≤ finMin a + Real.log (p jmin) / t := by
  have hZpos := weightedExpSum_pos p a hp t
  have hupp := weightedExpSum_le_min_exp p a hp hsum ht
  have hlow := min_witness_exp_le p a hp jmin hjmin t
  have hlogU : Real.log (weightedExpSum p a t) ≤ t * finMin a := by
    calc
      Real.log (weightedExpSum p a t) ≤ Real.log (Real.exp (t * finMin a)) :=
        Real.strictMonoOn_log.monotoneOn hZpos (Real.exp_pos _)
          hupp
      _ = t * finMin a := Real.log_exp _
  have hprodpos : 0 < p jmin * Real.exp (t * finMin a) :=
    mul_pos (hp jmin) (Real.exp_pos _)
  have hlogL : Real.log (p jmin) + t * finMin a ≤
      Real.log (weightedExpSum p a t) := by
    calc
      Real.log (p jmin) + t * finMin a =
          Real.log (p jmin * Real.exp (t * finMin a)) := by
        rw [Real.log_mul (hp jmin).ne' (Real.exp_pos _).ne', Real.log_exp]
      _ ≤ Real.log (weightedExpSum p a t) :=
        Real.strictMonoOn_log.monotoneOn hprodpos hZpos hlow
  constructor
  · unfold logSumExp
    rw [le_div_iff_of_neg ht]
    simpa [mul_comm] using hlogU
  · unfold logSumExp
    rw [div_le_iff_of_neg ht]
    calc
      (finMin a + Real.log (p jmin) / t) * t =
          Real.log (p jmin) + t * finMin a := by
        rw [add_mul, div_mul_cancel₀ _ ht.ne]
        ring
      _ ≤ Real.log (weightedExpSum p a t) := hlogL

/-- Positive-temperature sharp two-sided bound. -/
theorem logSumExp_bounds_pos {J : Type u} [Fintype J] [Nonempty J]
    (p a : J → ℝ) (hp : ∀ j, 0 < p j) (hsum : ∑ j, p j = 1)
    (jmax : J) (hjmax : a jmax = finMax a) {t : ℝ} (ht : 0 < t) :
    finMax a + Real.log (p jmax) / t ≤ logSumExp p a t ∧
      logSumExp p a t ≤ finMax a := by
  have hZpos := weightedExpSum_pos p a hp t
  have hupp := max_exp_le_weightedExpSum p a hp hsum ht
  have hlow := max_witness_exp_le p a hp jmax hjmax t
  have hlogU : Real.log (weightedExpSum p a t) ≤ t * finMax a := by
    calc
      Real.log (weightedExpSum p a t) ≤ Real.log (Real.exp (t * finMax a)) :=
        Real.strictMonoOn_log.monotoneOn hZpos (Real.exp_pos _) hupp
      _ = t * finMax a := Real.log_exp _
  have hprodpos : 0 < p jmax * Real.exp (t * finMax a) :=
    mul_pos (hp jmax) (Real.exp_pos _)
  have hlogL : Real.log (p jmax) + t * finMax a ≤
      Real.log (weightedExpSum p a t) := by
    calc
      Real.log (p jmax) + t * finMax a =
          Real.log (p jmax * Real.exp (t * finMax a)) := by
        rw [Real.log_mul (hp jmax).ne' (Real.exp_pos _).ne', Real.log_exp]
      _ ≤ Real.log (weightedExpSum p a t) :=
        Real.strictMonoOn_log.monotoneOn hprodpos hZpos hlow
  constructor
  · unfold logSumExp
    rw [le_div_iff₀ ht]
    calc
      (finMax a + Real.log (p jmax) / t) * t =
          Real.log (p jmax) + t * finMax a := by
        rw [add_mul, div_mul_cancel₀ _ ht.ne']
        ring
      _ ≤ Real.log (weightedExpSum p a t) := hlogL
  · unfold logSumExp
    rw [div_le_iff₀ ht]
    simpa [mul_comm] using hlogU

/-- Negative-temperature log-sum-exp converges to the finite minimum. -/
theorem tendsto_logSumExp_atBot {J : Type u} [Fintype J] [Nonempty J]
    (p a : J → ℝ) (hp : ∀ j, 0 < p j) (hsum : ∑ j, p j = 1) :
    Tendsto (logSumExp p a) atBot (𝓝 (finMin a)) := by
  obtain ⟨jmin, hjmin⟩ := finMin_mem a
  have hratio : Tendsto (fun t : ℝ => Real.log (p jmin) / t)
      atBot (𝓝 0) := tendsto_const_nhds.div_atBot tendsto_id
  have hupper : Tendsto
      (fun t : ℝ => finMin a + Real.log (p jmin) / t)
      atBot (𝓝 (finMin a)) := by
    simpa using tendsto_const_nhds.add hratio
  have hneg : ∀ᶠ t : ℝ in atBot, t < 0 :=
    eventually_lt_atBot (0 : ℝ)
  have hlower : ∀ᶠ t : ℝ in atBot, finMin a ≤ logSumExp p a t := by
    filter_upwards [hneg] with t ht
    exact (logSumExp_bounds_neg p a hp hsum jmin hjmin ht).1
  have hupp : ∀ᶠ t : ℝ in atBot,
      logSumExp p a t ≤ finMin a + Real.log (p jmin) / t := by
    filter_upwards [hneg] with t ht
    exact (logSumExp_bounds_neg p a hp hsum jmin hjmin ht).2
  exact tendsto_const_nhds.squeeze' hupper hlower hupp

/-- Positive-temperature log-sum-exp converges to the finite maximum. -/
theorem tendsto_logSumExp_atTop {J : Type u} [Fintype J] [Nonempty J]
    (p a : J → ℝ) (hp : ∀ j, 0 < p j) (hsum : ∑ j, p j = 1) :
    Tendsto (logSumExp p a) atTop (𝓝 (finMax a)) := by
  obtain ⟨jmax, hjmax⟩ := finMax_mem a
  have hratio : Tendsto (fun t : ℝ => Real.log (p jmax) / t)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hlowerLim : Tendsto
      (fun t : ℝ => finMax a + Real.log (p jmax) / t)
      atTop (𝓝 (finMax a)) := by
    simpa using tendsto_const_nhds.add hratio
  have hpos : ∀ᶠ t : ℝ in atTop, 0 < t :=
    eventually_gt_atTop (0 : ℝ)
  have hlower : ∀ᶠ t : ℝ in atTop,
      finMax a + Real.log (p jmax) / t ≤ logSumExp p a t := by
    filter_upwards [hpos] with t ht
    exact (logSumExp_bounds_pos p a hp hsum jmax hjmax ht).1
  have hupp : ∀ᶠ t : ℝ in atTop, logSumExp p a t ≤ finMax a := by
    filter_upwards [hpos] with t ht
    exact (logSumExp_bounds_pos p a hp hsum jmax hjmax ht).2
  exact hlowerLim.squeeze' tendsto_const_nhds hlower hupp

/-- Derivative of the positive exponential sum at zero. -/
theorem hasDerivAt_weightedExpSum_zero {J : Type u} [Fintype J]
    (p a : J → ℝ) :
    HasDerivAt (weightedExpSum p a) (∑ j, p j * a j) 0 := by
  classical
  unfold weightedExpSum
  apply HasDerivAt.fun_sum
  intro j _
  have hlin : HasDerivAt (fun t : ℝ => t * a j) (a j) 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) 0).mul_const (a j)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (t * a j)) (a j) 0 := by
    simpa using hlin.exp
  simpa [mul_comm] using hexp.const_mul (p j)

/-- The punctured-zero limit is the weighted arithmetic mean. -/
theorem tendsto_logSumExp_nhdsNE_zero {J : Type u}
    [Fintype J] [Nonempty J]
    (p a : J → ℝ) (hsum : ∑ j, p j = 1) :
    Tendsto (logSumExp p a) (𝓝[≠] 0) (𝓝 (∑ j, p j * a j)) := by
  let Z : ℝ → ℝ := weightedExpSum p a
  let m : ℝ := ∑ j, p j * a j
  have hZ0 : Z 0 = 1 := weightedExpSum_zero p a hsum
  have hZderiv : HasDerivAt Z m 0 := hasDerivAt_weightedExpSum_zero p a
  have hlogDeriv : HasDerivAt (fun t => Real.log (Z t)) m 0 := by
    convert hZderiv.log (by simp [hZ0]) using 1
    simp [hZ0]
  have hcontinuous := hlogDeriv.continuousAt_div
  have hlim : Tendsto
      (Function.update
        (fun t : ℝ => (Real.log (Z t) - Real.log (Z 0)) / (t - 0)) 0 m)
      (𝓝[≠] 0) (𝓝 m) :=
    by
      have hmono := hcontinuous.mono_left
        (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
      simpa using hmono
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by simpa using ht
  simp [Function.update, ht0, logSumExp, Z, hZ0]

/-- Literal bounds-and-limits package from the blueprint. -/
theorem logSumExpBoundsAndLimits {J : Type u} [Fintype J] [Nonempty J]
    (p a : J → ℝ) (hp : ∀ j, 0 < p j) (hsum : ∑ j, p j = 1)
    (jmin jmax : J) (hjmin : a jmin = finMin a)
    (hjmax : a jmax = finMax a) :
    (∀ t : ℝ, t < 0 →
      finMin a ≤ logSumExp p a t ∧
        logSumExp p a t ≤ finMin a + Real.log (p jmin) / t) ∧
    (∀ t : ℝ, 0 < t →
      finMax a + Real.log (p jmax) / t ≤ logSumExp p a t ∧
        logSumExp p a t ≤ finMax a) ∧
    Tendsto (logSumExp p a) atBot (𝓝 (finMin a)) ∧
    Tendsto (logSumExp p a) atTop (𝓝 (finMax a)) ∧
    Tendsto (logSumExp p a) (𝓝[≠] 0) (𝓝 (∑ j, p j * a j)) := by
  exact ⟨fun t ht => logSumExp_bounds_neg p a hp hsum jmin hjmin ht,
    fun t ht => logSumExp_bounds_pos p a hp hsum jmax hjmax ht,
    tendsto_logSumExp_atBot p a hp hsum,
    tendsto_logSumExp_atTop p a hp hsum,
    tendsto_logSumExp_nhdsNE_zero p a hsum⟩

end ConditionalEntropy
