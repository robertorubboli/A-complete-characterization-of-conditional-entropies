import ConditionalEntropy.ShannonKernelRegularity

/-!
# Order calculus for the dedicated Shannon escorts

These identities are the exact softmax calculus used by the dedicated
escort, neighbourhood, and localization estimates.  Unlike the generic
`BlockData` family, the first two Shannon bases contain the fixed factors
`theta.q` and `theta.p`; keeping their logarithms in `shannonLogBase` avoids
any hidden scale-dependent reparameterization.
-/

noncomputable section

open Filter Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

/-- Positive partition function of the three Shannon contributions. -/
def shannonPartition (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (alpha : ℝ) : ℝ :=
  ∑ j : Fin 3, shannonContribution theta n z j alpha

theorem shannonPartition_pos (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    0 < shannonPartition theta n z alpha :=
  sum_shannonContribution_pos theta n z alpha

theorem log_two_pos : 0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)

theorem log_two_le_shannonLogScale (n : ℕ) :
    Real.log (2 : ℝ) ≤ shannonLogScale n := by
  have hscale : (2 : ℝ) ≤ shannonScale n := by
    unfold shannonScale blockScale
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  exact Real.strictMonoOn_log.monotoneOn (by norm_num)
    (shannonScale_pos n) hscale

@[simp] theorem shannonLogBase_zero (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) :
    shannonLogBase theta n z 0 = Real.log theta.q := by
  rfl

@[simp] theorem shannonLogBase_one (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) :
    shannonLogBase theta n z 1 =
      shannonLogScale n + Real.log theta.p := by
  change Real.log (shannonScale n * theta.p) = _
  rw [Real.log_mul (shannonScale_pos n).ne' theta.p_pos.ne']
  rfl

@[simp] theorem shannonLogBase_two (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) :
    shannonLogBase theta n z 2 = 2 * shannonLogScale n := by
  change Real.log (shannonScale n ^ 2) = _
  rw [pow_two, Real.log_mul (shannonScale_pos n).ne'
    (shannonScale_pos n).ne']
  unfold shannonLogScale
  ring

@[simp] theorem shannonContribution_zero (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    shannonContribution theta n z 0 alpha =
      (shannonCount theta n 0 : ℝ) * Real.rpow theta.q alpha := by
  rfl

@[simp] theorem shannonContribution_one (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    shannonContribution theta n z 1 alpha =
      (shannonCount theta n 1 : ℝ) *
        Real.rpow (shannonScale n * theta.p) alpha := by
  rfl

@[simp] theorem shannonContribution_two (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    shannonContribution theta n z 2 alpha =
      (shannonCount theta n 2 : ℝ) *
        Real.rpow (shannonScale n ^ 2) alpha := by
  rfl

/-- Exact order derivative of one Shannon block contribution. -/
theorem hasDerivAt_shannonContribution (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (j : Fin 3) (alpha : ℝ) :
    HasDerivAt (shannonContribution theta n z j)
      (shannonContribution theta n z j alpha *
        shannonLogBase theta n z j) alpha := by
  let q : ℝ := shannonBase theta n z (shannonRepresentative theta n j)
  have hq : 0 < q :=
    shannonBase_pos theta n z (shannonRepresentative theta n j)
  have hp := (hasDerivAt_id (x := alpha)).const_rpow hq
  have hmul := hp.const_mul (shannonCount theta n j : ℝ)
  change HasDerivAt
    (fun y : ℝ ↦ (shannonCount theta n j : ℝ) * q ^ y)
    (((shannonCount theta n j : ℝ) * q ^ alpha) *
      Real.log q) alpha
  apply hmul.congr_deriv
  simp only [id_eq]
  ring

/-- Exact derivative of the Shannon partition function in the order
parameter. -/
theorem hasDerivAt_shannonPartition (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    HasDerivAt (shannonPartition theta n z)
      (∑ j : Fin 3, shannonContribution theta n z j alpha *
        shannonLogBase theta n z j) alpha := by
  unfold shannonPartition
  apply HasDerivAt.fun_sum
  intro j _hj
  exact hasDerivAt_shannonContribution theta n z j alpha

/-- The logarithmic escort mean is the corresponding unnormalized ratio. -/
theorem shannonEscortLogMean_eq_ratio (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    shannonEscortLogMean theta n z alpha =
      (∑ j : Fin 3, shannonContribution theta n z j alpha *
        shannonLogBase theta n z j) /
          shannonPartition theta n z alpha := by
  unfold shannonEscortLogMean shannonEscort shannonPartition
  calc
    ∑ j : Fin 3,
        (shannonContribution theta n z j alpha /
          ∑ l : Fin 3, shannonContribution theta n z l alpha) *
            shannonLogBase theta n z j =
      ∑ j : Fin 3,
        (shannonContribution theta n z j alpha *
          shannonLogBase theta n z j) /
            ∑ l : Fin 3, shannonContribution theta n z l alpha := by
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = _ := by rw [← Finset.sum_div]

/-- Exact softmax derivative of a dedicated Shannon escort. -/
theorem hasDerivAt_shannonEscort_order (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (j : Fin 3) (alpha : ℝ) :
    HasDerivAt (shannonEscort theta n z j)
      ((shannonLogBase theta n z j -
          shannonEscortLogMean theta n z alpha) *
        shannonEscort theta n z j alpha) alpha := by
  have hnum := hasDerivAt_shannonContribution theta n z j alpha
  have hden := hasDerivAt_shannonPartition theta n z alpha
  have hden0 : shannonPartition theta n z alpha ≠ 0 :=
    (shannonPartition_pos theta n z alpha).ne'
  have hquot : HasDerivAt
      (shannonContribution theta n z j / shannonPartition theta n z)
      ((shannonContribution theta n z j alpha *
            shannonLogBase theta n z j * shannonPartition theta n z alpha -
          shannonContribution theta n z j alpha *
            (∑ l : Fin 3, shannonContribution theta n z l alpha *
              shannonLogBase theta n z l)) /
        shannonPartition theta n z alpha ^ 2) alpha :=
    hnum.div hden hden0
  have hmean := shannonEscortLogMean_eq_ratio theta n z alpha
  apply hquot.congr_deriv
  rw [hmean]
  unfold shannonEscort shannonPartition at hden0 ⊢
  field_simp [hden0]

theorem deriv_shannonEscort_order (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (j : Fin 3) (alpha : ℝ) :
    deriv (fun s ↦ shannonEscort theta n z j s) alpha =
      (shannonLogBase theta n z j -
          shannonEscortLogMean theta n z alpha) *
        shannonEscort theta n z j alpha :=
  (hasDerivAt_shannonEscort_order theta n z j alpha).deriv

/-- Differentiation of the Shannon escort velocity mean in its order
parameter. -/
theorem hasDerivAt_shannonMean_order (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    HasDerivAt (fun s ↦ shannonMean theta n z s)
      (∑ j : Fin 3,
        deriv (fun s ↦ shannonEscort theta n z j s) alpha *
          shannonBlockVelocity theta n z j) alpha := by
  unfold shannonMean
  apply HasDerivAt.fun_sum
  intro j _hj
  have hj := (hasDerivAt_shannonEscort_order theta n z j alpha).mul_const
    (shannonBlockVelocity theta n z j)
  apply hj.congr_deriv
  rw [deriv_shannonEscort_order]

theorem deriv_shannonMean_order (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    deriv (fun s ↦ shannonMean theta n z s) alpha =
      ∑ j : Fin 3,
        deriv (fun s ↦ shannonEscort theta n z j s) alpha *
          shannonBlockVelocity theta n z j :=
  (hasDerivAt_shannonMean_order theta n z alpha).deriv

/-- Differentiation of the Shannon escort second velocity moment. -/
theorem hasDerivAt_shannonSecond_order (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    HasDerivAt (fun s ↦ shannonSecond theta n z s)
      (∑ j : Fin 3,
        deriv (fun s ↦ shannonEscort theta n z j s) alpha *
          shannonBlockVelocity theta n z j ^ 2) alpha := by
  unfold shannonSecond
  apply HasDerivAt.fun_sum
  intro j _hj
  have hj := (hasDerivAt_shannonEscort_order theta n z j alpha).mul_const
    (shannonBlockVelocity theta n z j ^ 2)
  apply hj.congr_deriv
  rw [deriv_shannonEscort_order]

theorem deriv_shannonSecond_order (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    deriv (fun s ↦ shannonSecond theta n z s) alpha =
      ∑ j : Fin 3,
        deriv (fun s ↦ shannonEscort theta n z j s) alpha *
          shannonBlockVelocity theta n z j ^ 2 :=
  (hasDerivAt_shannonSecond_order theta n z alpha).deriv

/-- Centering an arbitrary Shannon escort average at block `k` removes the
`k` term exactly. -/
theorem shannonEscortWeighted_sub_eq_sum_erase (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (alpha : ℝ) (k : Fin 3)
    (v : Fin 3 → ℝ) :
    (∑ j, shannonEscort theta n z j alpha * v j) - v k =
      ∑ j ∈ Finset.univ.erase k,
        shannonEscort theta n z j alpha * (v j - v k) := by
  have hsum := sum_shannonEscort theta n z alpha
  calc
    (∑ j, shannonEscort theta n z j alpha * v j) - v k =
        (∑ j, shannonEscort theta n z j alpha * v j) -
          v k * (∑ j, shannonEscort theta n z j alpha) := by
      rw [hsum]
      ring
    _ = ∑ j, shannonEscort theta n z j alpha * (v j - v k) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    _ = ∑ j ∈ Finset.univ.erase k,
        shannonEscort theta n z j alpha * (v j - v k) := by
      symm
      exact Finset.sum_erase Finset.univ (by simp)

/-- An outside-mass estimate for an arbitrary Shannon escort average. -/
theorem abs_shannonEscortWeighted_sub_le_outside (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (alpha : ℝ) (k : Fin 3)
    (v : Fin 3 → ℝ) (D : ℝ) (hD : ∀ j, |v j - v k| ≤ D) :
    |(∑ j, shannonEscort theta n z j alpha * v j) - v k| ≤
      D * (∑ j ∈ Finset.univ.erase k,
        shannonEscort theta n z j alpha) := by
  rw [shannonEscortWeighted_sub_eq_sum_erase]
  calc
    |∑ j ∈ Finset.univ.erase k,
        shannonEscort theta n z j alpha * (v j - v k)| ≤
        ∑ j ∈ Finset.univ.erase k,
          |shannonEscort theta n z j alpha * (v j - v k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.univ.erase k,
        shannonEscort theta n z j alpha * D := by
      apply Finset.sum_le_sum
      intro j _hj
      rw [abs_mul, abs_of_nonneg (shannonEscort_nonneg theta n z j alpha)]
      exact mul_le_mul_of_nonneg_left (hD j)
        (shannonEscort_nonneg theta n z j alpha)
    _ = D * (∑ j ∈ Finset.univ.erase k,
        shannonEscort theta n z j alpha) := by
      rw [← Finset.sum_mul]
      ring

theorem abs_shannonMean_sub_le_outside (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) (k : Fin 3) (U : ℝ)
    (hu : ∀ j, |shannonBlockVelocity theta n z j| ≤ U) :
    |shannonMean theta n z alpha - shannonBlockVelocity theta n z k| ≤
      (2 * U) * (∑ j ∈ Finset.univ.erase k,
        shannonEscort theta n z j alpha) := by
  unfold shannonMean
  apply abs_shannonEscortWeighted_sub_le_outside theta n z alpha k
    (shannonBlockVelocity theta n z) (2 * U)
  intro j
  calc
    |shannonBlockVelocity theta n z j -
        shannonBlockVelocity theta n z k| ≤
      |shannonBlockVelocity theta n z j| +
        |shannonBlockVelocity theta n z k| := abs_sub _ _
    _ ≤ U + U := add_le_add (hu j) (hu k)
    _ = 2 * U := by ring

theorem abs_shannonSecond_sub_le_outside (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) (k : Fin 3) (U : ℝ) (hU : 0 ≤ U)
    (hu : ∀ j, |shannonBlockVelocity theta n z j| ≤ U) :
    |shannonSecond theta n z alpha -
        shannonBlockVelocity theta n z k ^ 2| ≤
      (2 * U ^ 2) * (∑ j ∈ Finset.univ.erase k,
        shannonEscort theta n z j alpha) := by
  unfold shannonSecond
  apply abs_shannonEscortWeighted_sub_le_outside theta n z alpha k
    (fun j ↦ shannonBlockVelocity theta n z j ^ 2) (2 * U ^ 2)
  intro j
  have hj : shannonBlockVelocity theta n z j ^ 2 ≤ U ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_nonneg hU] using hu j)
  have hk : shannonBlockVelocity theta n z k ^ 2 ≤ U ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_nonneg hU] using hu k)
  calc
    |shannonBlockVelocity theta n z j ^ 2 -
        shannonBlockVelocity theta n z k ^ 2| ≤
      |shannonBlockVelocity theta n z j ^ 2| +
        |shannonBlockVelocity theta n z k ^ 2| := abs_sub _ _
    _ = shannonBlockVelocity theta n z j ^ 2 +
        shannonBlockVelocity theta n z k ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    _ ≤ U ^ 2 + U ^ 2 := add_le_add hj hk
    _ = 2 * U ^ 2 := by ring

theorem sum_shannonEscort_mul_sub_sq (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha c : ℝ) :
    ∑ j, shannonEscort theta n z j alpha *
        (shannonBlockVelocity theta n z j - c) ^ 2 =
      shannonSecond theta n z alpha -
        2 * c * shannonMean theta n z alpha + c ^ 2 := by
  have hsum := sum_shannonEscort theta n z alpha
  simp_rw [show ∀ j : Fin 3,
      shannonEscort theta n z j alpha *
          (shannonBlockVelocity theta n z j - c) ^ 2 =
        (shannonEscort theta n z j alpha *
            shannonBlockVelocity theta n z j ^ 2 -
          (2 * c) * (shannonEscort theta n z j alpha *
            shannonBlockVelocity theta n z j)) +
          c ^ 2 * shannonEscort theta n z j alpha by
    intro j
    ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hsum]
  simp only [shannonSecond, shannonMean]
  ring

theorem shannonVar_eq_sum_centered_sq (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    shannonVar theta n z alpha =
      ∑ j, shannonEscort theta n z j alpha *
        (shannonBlockVelocity theta n z j -
          shannonMean theta n z alpha) ^ 2 := by
  rw [sum_shannonEscort_mul_sub_sq]
  unfold shannonVar
  ring

theorem shannonVar_nonneg (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    0 ≤ shannonVar theta n z alpha := by
  rw [shannonVar_eq_sum_centered_sq]
  exact Finset.sum_nonneg fun j _hj ↦
    mul_nonneg (shannonEscort_nonneg theta n z j alpha) (sq_nonneg _)

theorem shannonVar_le_outside (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) (k : Fin 3) (U : ℝ) (hU : 0 ≤ U)
    (hu : ∀ j, |shannonBlockVelocity theta n z j| ≤ U) :
    shannonVar theta n z alpha ≤
      (4 * U ^ 2) * (∑ j ∈ Finset.univ.erase k,
        shannonEscort theta n z j alpha) := by
  have hsquare := sum_shannonEscort_mul_sub_sq theta n z alpha
    (shannonBlockVelocity theta n z k)
  have hcenter : shannonVar theta n z alpha ≤
      shannonSecond theta n z alpha -
        2 * shannonBlockVelocity theta n z k *
          shannonMean theta n z alpha +
        shannonBlockVelocity theta n z k ^ 2 := by
    unfold shannonVar
    nlinarith [sq_nonneg (shannonMean theta n z alpha -
      shannonBlockVelocity theta n z k)]
  calc
    shannonVar theta n z alpha ≤
        shannonSecond theta n z alpha -
          2 * shannonBlockVelocity theta n z k *
            shannonMean theta n z alpha +
          shannonBlockVelocity theta n z k ^ 2 := hcenter
    _ = ∑ j, shannonEscort theta n z j alpha *
        (shannonBlockVelocity theta n z j -
          shannonBlockVelocity theta n z k) ^ 2 := hsquare.symm
    _ = ∑ j ∈ Finset.univ.erase k,
        shannonEscort theta n z j alpha *
          (shannonBlockVelocity theta n z j -
            shannonBlockVelocity theta n z k) ^ 2 := by
      symm
      exact Finset.sum_erase Finset.univ (by simp)
    _ ≤ ∑ j ∈ Finset.univ.erase k,
        shannonEscort theta n z j alpha * (4 * U ^ 2) := by
      apply Finset.sum_le_sum
      intro j _hj
      have hdiff : |shannonBlockVelocity theta n z j -
          shannonBlockVelocity theta n z k| ≤ 2 * U := by
        calc
          |shannonBlockVelocity theta n z j -
              shannonBlockVelocity theta n z k| ≤
            |shannonBlockVelocity theta n z j| +
              |shannonBlockVelocity theta n z k| := abs_sub _ _
          _ ≤ U + U := add_le_add (hu j) (hu k)
          _ = 2 * U := by ring
      have hsquareDiff :
          (shannonBlockVelocity theta n z j -
            shannonBlockVelocity theta n z k) ^ 2 ≤ (2 * U) ^ 2 :=
        sq_le_sq.mpr (by
          rw [abs_of_nonneg (mul_nonneg (by norm_num) hU)]
          exact hdiff)
      have hsquareDiff' :
          (shannonBlockVelocity theta n z j -
            shannonBlockVelocity theta n z k) ^ 2 ≤ 4 * U ^ 2 := by
        nlinarith
      exact mul_le_mul_of_nonneg_left hsquareDiff'
        (shannonEscort_nonneg theta n z j alpha)
    _ = (4 * U ^ 2) * (∑ j ∈ Finset.univ.erase k,
        shannonEscort theta n z j alpha) := by
      rw [← Finset.sum_mul]
      ring

theorem abs_shannonMean_le (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha U : ℝ)
    (hu : ∀ j, |shannonBlockVelocity theta n z j| ≤ U) :
    |shannonMean theta n z alpha| ≤ U := by
  unfold shannonMean
  calc
    |∑ j : Fin 3, shannonEscort theta n z j alpha *
        shannonBlockVelocity theta n z j| ≤
      ∑ j : Fin 3, |shannonEscort theta n z j alpha *
        shannonBlockVelocity theta n z j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, shannonEscort theta n z j alpha * U := by
      apply Finset.sum_le_sum
      intro j _hj
      rw [abs_mul, abs_of_nonneg (shannonEscort_nonneg theta n z j alpha)]
      exact mul_le_mul_of_nonneg_left (hu j)
        (shannonEscort_nonneg theta n z j alpha)
    _ = U := by
      rw [← Finset.sum_mul, sum_shannonEscort, one_mul]

/-- Exact finite-order first Shannon kernel away from order one. -/
theorem shannonKOne_finite (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) {alpha : ℝ} (h_alpha : 0 < alpha)
    (h_one : alpha ≠ 1) :
    shannonKOne theta n z (finiteParam alpha) =
      singularWeight (finiteParam alpha) *
        (shannonMean theta n z alpha - shannonMean theta n z 1) := by
  letI := shannonIndexNonempty theta n
  rw [shannonKOne, entropyLineFirst_finite_zero _ h_alpha h_one,
    escortMean_shannonLine_zero, escortMean_shannonLine_zero]

/-- Exact min-entropy endpoint formula for the dedicated Shannon line. -/
theorem shannonKOne_top (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) :
    shannonKOne theta n z ⊤ = shannonMean theta n z 1 - z.2 := by
  letI := shannonIndexNonempty theta n
  obtain ⟨epsilon, hepsilon, hfixed⟩ :=
    exists_fixedMaxCoordinate_shannonLine theta n z
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := by
    constructor <;> linarith
  rw [shannonKOne,
    entropyLineFirst_top_on (shannonLineData theta n z) isOpen_Ioo hfixed hzero,
    escortMean_shannonLine_zero, effectiveVelocity_shannonLine_zero]
  rfl

/-- Finite diameter of the three logarithmic Shannon bases. -/
def shannonLogDiameter (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) : ℝ :=
  ∑ j : Fin 3, ∑ l : Fin 3,
    |shannonLogBase theta n z j - shannonLogBase theta n z l|

/-- A scale-independent coefficient controlling all three logarithmic bases. -/
def shannonLogBaseCoeff (theta : ShannonData) : ℝ :=
  2 + |Real.log theta.q| / Real.log 2 +
    |Real.log theta.p| / Real.log 2

theorem shannonLogBaseCoeff_nonneg (theta : ShannonData) :
    0 ≤ shannonLogBaseCoeff theta := by
  unfold shannonLogBaseCoeff
  positivity

theorem abs_shannonLogBase_le_coeff (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (j : Fin 3) :
    |shannonLogBase theta n z j| ≤
      shannonLogBaseCoeff theta * shannonLogScale n := by
  let L := shannonLogScale n
  let ltwo := Real.log (2 : ℝ)
  let aq := |Real.log theta.q|
  let ap := |Real.log theta.p|
  have hL : 0 ≤ L := (shannonLogScale_pos n).le
  have htwo : 0 < ltwo := log_two_pos
  have htwoL : ltwo ≤ L := log_two_le_shannonLogScale n
  have haq : aq ≤ (aq / ltwo) * L := by
    calc
      aq = (aq / ltwo) * ltwo := by field_simp [htwo.ne']
      _ ≤ (aq / ltwo) * L :=
        mul_le_mul_of_nonneg_left htwoL (div_nonneg (abs_nonneg _) htwo.le)
  have heap : ap ≤ (ap / ltwo) * L := by
    calc
      ap = (ap / ltwo) * ltwo := by field_simp [htwo.ne']
      _ ≤ (ap / ltwo) * L :=
        mul_le_mul_of_nonneg_left htwoL (div_nonneg (abs_nonneg _) htwo.le)
  have haqdiv : 0 ≤ aq / ltwo := div_nonneg (abs_nonneg _) htwo.le
  have hapdiv : 0 ≤ ap / ltwo := div_nonneg (abs_nonneg _) htwo.le
  have hqCoeff : aq / ltwo ≤ shannonLogBaseCoeff theta := by
    dsimp only [shannonLogBaseCoeff, ltwo, aq, ap]
    linarith
  have hpCoeff : 1 + ap / ltwo ≤ shannonLogBaseCoeff theta := by
    dsimp only [shannonLogBaseCoeff, ltwo, aq, ap]
    linarith
  have htwoCoeff : 2 ≤ shannonLogBaseCoeff theta := by
    dsimp only [shannonLogBaseCoeff, ltwo, aq, ap]
    linarith
  fin_cases j
  · change |Real.log theta.q| ≤
      shannonLogBaseCoeff theta * shannonLogScale n
    calc
      |Real.log theta.q| = aq := rfl
      _ ≤ (aq / ltwo) * L := haq
      _ ≤ shannonLogBaseCoeff theta * L :=
        mul_le_mul_of_nonneg_right hqCoeff hL
  · change |Real.log (shannonScale n * theta.p)| ≤
      shannonLogBaseCoeff theta * shannonLogScale n
    rw [Real.log_mul (shannonScale_pos n).ne' theta.p_pos.ne']
    calc
      |shannonLogScale n + Real.log theta.p| ≤
          L + ap := by
        simpa only [L, ap, abs_of_nonneg hL] using
          (abs_add_le (shannonLogScale n) (Real.log theta.p))
      _ ≤ L + (ap / ltwo) * L := add_le_add le_rfl heap
      _ = (1 + ap / ltwo) * L := by ring
      _ ≤ shannonLogBaseCoeff theta * L :=
        mul_le_mul_of_nonneg_right hpCoeff hL
  · change |Real.log (shannonScale n ^ 2)| ≤
      shannonLogBaseCoeff theta * shannonLogScale n
    rw [pow_two, Real.log_mul (shannonScale_pos n).ne'
      (shannonScale_pos n).ne']
    have hlog : 0 ≤ Real.log (shannonScale n) := by
      simpa only [L, shannonLogScale] using hL
    rw [abs_of_nonneg (add_nonneg hlog hlog)]
    calc
      Real.log (shannonScale n) + Real.log (shannonScale n) =
          2 * Real.log (shannonScale n) := by ring
      _ ≤ shannonLogBaseCoeff theta * Real.log (shannonScale n) :=
        mul_le_mul_of_nonneg_right htwoCoeff hlog

/-- The logarithmic diameter grows at most linearly in the scale logarithm. -/
theorem shannonLogDiameter_le (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) :
    shannonLogDiameter theta n z ≤
      (18 * shannonLogBaseCoeff theta) * shannonLogScale n := by
  unfold shannonLogDiameter
  calc
    ∑ j : Fin 3, ∑ l : Fin 3,
        |shannonLogBase theta n z j - shannonLogBase theta n z l| ≤
      ∑ _j : Fin 3, ∑ _l : Fin 3,
        (2 * shannonLogBaseCoeff theta) * shannonLogScale n := by
      apply Finset.sum_le_sum
      intro j _hj
      apply Finset.sum_le_sum
      intro l _hl
      calc
        |shannonLogBase theta n z j - shannonLogBase theta n z l| ≤
            |shannonLogBase theta n z j| +
              |shannonLogBase theta n z l| := abs_sub _ _
        _ ≤ shannonLogBaseCoeff theta * shannonLogScale n +
            shannonLogBaseCoeff theta * shannonLogScale n :=
          add_le_add (abs_shannonLogBase_le_coeff theta n z j)
            (abs_shannonLogBase_le_coeff theta n z l)
        _ = (2 * shannonLogBaseCoeff theta) * shannonLogScale n := by
          ring
    _ = (18 * shannonLogBaseCoeff theta) * shannonLogScale n := by
      simp only [Fin.sum_univ_three]
      ring

theorem shannonLogDiameter_nonneg (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) : 0 ≤ shannonLogDiameter theta n z := by
  exact Finset.sum_nonneg fun j _hj ↦
    Finset.sum_nonneg fun l _hl ↦ abs_nonneg _

theorem abs_shannonLogBase_sub_le_diameter (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (j l : Fin 3) :
    |shannonLogBase theta n z j - shannonLogBase theta n z l| ≤
      shannonLogDiameter theta n z := by
  have hinner :
      |shannonLogBase theta n z j - shannonLogBase theta n z l| ≤
        ∑ r : Fin 3,
          |shannonLogBase theta n z j - shannonLogBase theta n z r| := by
    exact Finset.single_le_sum (s := Finset.univ)
      (fun r _hr ↦ abs_nonneg
        (shannonLogBase theta n z j - shannonLogBase theta n z r))
      (Finset.mem_univ l)
  have houter :
      (∑ r : Fin 3,
          |shannonLogBase theta n z j - shannonLogBase theta n z r|) ≤
        shannonLogDiameter theta n z := by
    exact Finset.single_le_sum (s := Finset.univ)
      (fun q _hq ↦ Finset.sum_nonneg fun r _hr ↦ abs_nonneg
        (shannonLogBase theta n z q - shannonLogBase theta n z r))
      (Finset.mem_univ j)
  exact hinner.trans houter

theorem shannonEscort_le_one (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (j : Fin 3) (alpha : ℝ) :
    shannonEscort theta n z j alpha ≤ 1 := by
  have hj : shannonEscort theta n z j alpha ≤
      ∑ l : Fin 3, shannonEscort theta n z l alpha :=
    Finset.single_le_sum
      (fun l _hl ↦ shannonEscort_nonneg theta n z l alpha)
      (Finset.mem_univ j)
  simpa only [sum_shannonEscort] using hj

theorem shannonOutsideMass_le_one (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (k : Fin 3) (alpha : ℝ) :
    ∑ j ∈ Finset.univ.erase k, shannonEscort theta n z j alpha ≤ 1 := by
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun j ↦ shannonEscort theta n z j alpha) (Finset.mem_univ k)
  have hsum := sum_shannonEscort theta n z alpha
  have hk := shannonEscort_nonneg theta n z k alpha
  linarith

theorem sum_shannonEscort_erase_two (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    ∑ j ∈ Finset.univ.erase (2 : Fin 3),
        shannonEscort theta n z j alpha =
      shannonEscort theta n z 0 alpha +
        shannonEscort theta n z 1 alpha := by
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun j ↦ shannonEscort theta n z j alpha)
    (Finset.mem_univ (2 : Fin 3))
  rw [Fin.sum_univ_three] at hsplit
  linarith

theorem abs_shannonLogBase_sub_escortMean_le (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (j : Fin 3) (alpha : ℝ) :
    |shannonLogBase theta n z j -
        shannonEscortLogMean theta n z alpha| ≤
      shannonLogDiameter theta n z := by
  have hcenter := abs_shannonEscortWeighted_sub_le_outside theta n z alpha j
    (shannonLogBase theta n z) (shannonLogDiameter theta n z)
    (fun l ↦ abs_shannonLogBase_sub_le_diameter theta n z l j)
  rw [abs_sub_comm] at hcenter
  calc
    |shannonLogBase theta n z j -
        shannonEscortLogMean theta n z alpha| ≤
      shannonLogDiameter theta n z *
        (∑ l ∈ Finset.univ.erase j,
          shannonEscort theta n z l alpha) := by
      simpa only [shannonEscortLogMean] using hcenter
    _ ≤ shannonLogDiameter theta n z * 1 :=
      mul_le_mul_of_nonneg_left
        (shannonOutsideMass_le_one theta n z j alpha)
        (shannonLogDiameter_nonneg theta n z)
    _ = shannonLogDiameter theta n z := mul_one _

theorem abs_dominantShannonLogBase_sub_escortMean_le
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) (k : Fin 3)
    (alpha : ℝ) :
    |shannonLogBase theta n z k -
        shannonEscortLogMean theta n z alpha| ≤
      shannonLogDiameter theta n z *
        (∑ j ∈ Finset.univ.erase k,
          shannonEscort theta n z j alpha) := by
  have hcenter := abs_shannonEscortWeighted_sub_le_outside theta n z alpha k
    (shannonLogBase theta n z) (shannonLogDiameter theta n z)
    (fun j ↦ abs_shannonLogBase_sub_le_diameter theta n z j k)
  rw [abs_sub_comm]
  simpa only [shannonEscortLogMean] using hcenter

theorem abs_deriv_shannonEscort_order (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (j : Fin 3) (alpha : ℝ) :
    |deriv (fun s ↦ shannonEscort theta n z j s) alpha| =
      shannonEscort theta n z j alpha *
        |shannonLogBase theta n z j -
          shannonEscortLogMean theta n z alpha| := by
  rw [deriv_shannonEscort_order, abs_mul,
    abs_of_nonneg (shannonEscort_nonneg theta n z j alpha)]
  ring

theorem sum_abs_deriv_shannonEscort_order_le_outside
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) (k : Fin 3)
    (alpha : ℝ) :
    ∑ j : Fin 3, |deriv (fun s ↦ shannonEscort theta n z j s) alpha| ≤
      (2 * shannonLogDiameter theta n z) *
        (∑ j ∈ Finset.univ.erase k,
          shannonEscort theta n z j alpha) := by
  let D := shannonLogDiameter theta n z
  let R := ∑ j ∈ Finset.univ.erase k,
    shannonEscort theta n z j alpha
  have hD : 0 ≤ D := shannonLogDiameter_nonneg theta n z
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact Finset.sum_nonneg fun j _hj ↦
      shannonEscort_nonneg theta n z j alpha
  have hk : |deriv (fun s ↦ shannonEscort theta n z k s) alpha| ≤
      D * R := by
    rw [abs_deriv_shannonEscort_order]
    have hc : |shannonLogBase theta n z k -
        shannonEscortLogMean theta n z alpha| ≤ D * R := by
      simpa only [D, R] using
        abs_dominantShannonLogBase_sub_escortMean_le theta n z k alpha
    calc
      shannonEscort theta n z k alpha *
          |shannonLogBase theta n z k -
            shannonEscortLogMean theta n z alpha| ≤
        1 * (D * R) :=
          mul_le_mul (shannonEscort_le_one theta n z k alpha) hc
            (abs_nonneg _) (by norm_num)
      _ = D * R := by ring
  have hout :
      ∑ j ∈ Finset.univ.erase k,
          |deriv (fun s ↦ shannonEscort theta n z j s) alpha| ≤
        D * R := by
    calc
      ∑ j ∈ Finset.univ.erase k,
          |deriv (fun s ↦ shannonEscort theta n z j s) alpha| ≤
        ∑ j ∈ Finset.univ.erase k,
          D * shannonEscort theta n z j alpha := by
        apply Finset.sum_le_sum
        intro j _hj
        rw [abs_deriv_shannonEscort_order]
        have hc := abs_shannonLogBase_sub_escortMean_le theta n z j alpha
        calc
          shannonEscort theta n z j alpha *
              |shannonLogBase theta n z j -
                shannonEscortLogMean theta n z alpha| ≤
            shannonEscort theta n z j alpha * D :=
              mul_le_mul_of_nonneg_left hc
                (shannonEscort_nonneg theta n z j alpha)
          _ = D * shannonEscort theta n z j alpha := by ring
      _ = D * R := by
        dsimp only [R]
        rw [Finset.mul_sum]
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun j ↦ |deriv (fun s ↦ shannonEscort theta n z j s) alpha|)
    (Finset.mem_univ k)
  calc
    ∑ j : Fin 3, |deriv (fun s ↦ shannonEscort theta n z j s) alpha| =
        |deriv (fun s ↦ shannonEscort theta n z k s) alpha| +
          ∑ j ∈ Finset.univ.erase k,
            |deriv (fun s ↦ shannonEscort theta n z j s) alpha| :=
      hsplit.symm
    _ ≤ D * R + D * R := add_le_add hk hout
    _ = (2 * shannonLogDiameter theta n z) *
        (∑ j ∈ Finset.univ.erase k,
          shannonEscort theta n z j alpha) := by
      dsimp only [D, R]
      ring

theorem abs_deriv_shannonMean_order_le (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (U alpha : ℝ) (_hU : 0 ≤ U)
    (hu : ∀ j, |shannonBlockVelocity theta n z j| ≤ U) :
    |deriv (fun s ↦ shannonMean theta n z s) alpha| ≤
      U * ∑ j : Fin 3,
        |deriv (fun s ↦ shannonEscort theta n z j s) alpha| := by
  rw [deriv_shannonMean_order]
  calc
    |∑ j : Fin 3,
        deriv (fun s ↦ shannonEscort theta n z j s) alpha *
          shannonBlockVelocity theta n z j| ≤
      ∑ j : Fin 3,
        |deriv (fun s ↦ shannonEscort theta n z j s) alpha *
          shannonBlockVelocity theta n z j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3,
        |deriv (fun s ↦ shannonEscort theta n z j s) alpha| * U := by
      apply Finset.sum_le_sum
      intro j _hj
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hu j) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem abs_deriv_shannonSecond_order_le (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (U alpha : ℝ) (_hU : 0 ≤ U)
    (hu : ∀ j, |shannonBlockVelocity theta n z j| ≤ U) :
    |deriv (fun s ↦ shannonSecond theta n z s) alpha| ≤
      U ^ 2 * ∑ j : Fin 3,
        |deriv (fun s ↦ shannonEscort theta n z j s) alpha| := by
  rw [deriv_shannonSecond_order]
  calc
    |∑ j : Fin 3,
        deriv (fun s ↦ shannonEscort theta n z j s) alpha *
          shannonBlockVelocity theta n z j ^ 2| ≤
      ∑ j : Fin 3,
        |deriv (fun s ↦ shannonEscort theta n z j s) alpha *
          shannonBlockVelocity theta n z j ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3,
        |deriv (fun s ↦ shannonEscort theta n z j s) alpha| * U ^ 2 := by
      apply Finset.sum_le_sum
      intro j _hj
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hu j) 2)
        (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end ConditionalEntropy
