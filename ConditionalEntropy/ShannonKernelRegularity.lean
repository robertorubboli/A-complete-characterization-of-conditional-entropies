import ConditionalEntropy.ShannonAlgebra

/-!
# Algebraic regularity of the Shannon kernels

At the base point the three Shannon escort weights do not depend on the
velocity parameter.  Consequently the first entropy kernel is linear in the
two velocity coordinates and the second is a quadratic form.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

theorem shannonEscort_parameter_independent (theta : ShannonData) (n : ℕ)
    (z w : ℝ × ℝ) (j : Fin 3) (alpha : ℝ) :
    shannonEscort theta n z j alpha = shannonEscort theta n w j alpha := by
  rfl

theorem shannonBlockVelocity_add (theta : ShannonData) (n : ℕ)
    (z w : ℝ × ℝ) (j : Fin 3) :
    shannonBlockVelocity theta n (z + w) j =
      shannonBlockVelocity theta n z j +
        shannonBlockVelocity theta n w j := by
  rcases j with ⟨j, hj⟩
  interval_cases j <;>
    simp [shannonBlockVelocity, shannonVelocity, shannonRepresentative] <;> ring

theorem shannonBlockVelocity_smul (theta : ShannonData) (n : ℕ)
    (c : ℝ) (z : ℝ × ℝ) (j : Fin 3) :
    shannonBlockVelocity theta n (c • z) j =
      c * shannonBlockVelocity theta n z j := by
  rcases j with ⟨j, hj⟩
  interval_cases j <;>
    simp [shannonBlockVelocity, shannonVelocity, shannonRepresentative,
      smul_eq_mul] <;> ring

theorem shannonVelocity_add (theta : ShannonData) (n : ℕ)
    (z w : ℝ × ℝ) (i : ShannonIndex theta n) :
    shannonVelocity theta n (z + w) i =
      shannonVelocity theta n z i + shannonVelocity theta n w i := by
  rcases i with ⟨j, i⟩
  fin_cases j <;> simp [shannonVelocity] <;> ring

theorem shannonVelocity_smul (theta : ShannonData) (n : ℕ)
    (c : ℝ) (z : ℝ × ℝ) (i : ShannonIndex theta n) :
    shannonVelocity theta n (c • z) i =
      c * shannonVelocity theta n z i := by
  rcases i with ⟨j, i⟩
  fin_cases j <;> simp [shannonVelocity, smul_eq_mul] <;> ring

theorem shannonMean_add (theta : ShannonData) (n : ℕ)
    (z w : ℝ × ℝ) (alpha : ℝ) :
    shannonMean theta n (z + w) alpha =
      shannonMean theta n z alpha + shannonMean theta n w alpha := by
  unfold shannonMean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [shannonEscort_parameter_independent theta n (z + w) z,
    shannonEscort_parameter_independent theta n w z,
    shannonBlockVelocity_add]
  ring

theorem shannonMean_smul (theta : ShannonData) (n : ℕ)
    (c : ℝ) (z : ℝ × ℝ) (alpha : ℝ) :
    shannonMean theta n (c • z) alpha =
      c * shannonMean theta n z alpha := by
  unfold shannonMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [shannonEscort_parameter_independent theta n (c • z) z,
    shannonBlockVelocity_smul]
  ring

theorem continuous_shannonMean (theta : ShannonData) (n : ℕ)
    (alpha : ℝ) : Continuous (fun z : ℝ × ℝ ↦
      shannonMean theta n z alpha) := by
  have heq : (fun z : ℝ × ℝ ↦ shannonMean theta n z alpha) =
      fun z ↦ ∑ j : Fin 3, shannonEscort theta n (0, 0) j alpha *
        shannonBlockVelocity theta n z j := by
    funext z
    unfold shannonMean
    apply Finset.sum_congr rfl
    intro j _hj
    rw [shannonEscort_parameter_independent theta n z (0, 0)]
  rw [heq]
  unfold shannonBlockVelocity shannonVelocity
  fun_prop

theorem continuous_shannonSecond (theta : ShannonData) (n : ℕ)
    (alpha : ℝ) : Continuous (fun z : ℝ × ℝ ↦
      shannonSecond theta n z alpha) := by
  have heq : (fun z : ℝ × ℝ ↦ shannonSecond theta n z alpha) =
      fun z ↦ ∑ j : Fin 3, shannonEscort theta n (0, 0) j alpha *
        shannonBlockVelocity theta n z j ^ 2 := by
    funext z
    unfold shannonSecond
    apply Finset.sum_congr rfl
    intro j _hj
    rw [shannonEscort_parameter_independent theta n z (0, 0)]
  rw [heq]
  unfold shannonBlockVelocity shannonVelocity
  fun_prop

theorem continuous_shannonVar (theta : ShannonData) (n : ℕ)
    (alpha : ℝ) : Continuous (fun z : ℝ × ℝ ↦
      shannonVar theta n z alpha) := by
  unfold shannonVar
  exact (continuous_shannonSecond theta n alpha).sub
    ((continuous_shannonMean theta n alpha).pow 2)

theorem lineProb_shannonLine_zero_parameter_independent
    (theta : ShannonData) (n : ℕ) (z w : ℝ × ℝ) :
    letI := shannonIndexNonempty theta n
    lineProb (shannonLineData theta n z) 0 =
      lineProb (shannonLineData theta n w) 0 := by
  letI := shannonIndexNonempty theta n
  apply Subtype.ext
  funext i
  rw [lineProb_apply_of_positive _ (linePositiveZero _) i,
    lineProb_apply_of_positive _ (linePositiveZero _) i]
  simp [lineRaw, lineMass, shannonLineData, shannonBase]

theorem lineProb_shannonLine_zero_apply_parameter_independent
    (theta : ShannonData) (n : ℕ) (z w : ℝ × ℝ)
    (i : ShannonIndex theta n) :
    letI := shannonIndexNonempty theta n
    (lineProb (shannonLineData theta n z) 0).1 i =
      (lineProb (shannonLineData theta n w) 0).1 i := by
  letI := shannonIndexNonempty theta n
  exact congrArg (fun P : ProbVec (ShannonIndex theta n) ↦ P.1 i)
    (lineProb_shannonLine_zero_parameter_independent theta n z w)

@[simp] theorem effectiveVelocity_shannonLine_zero
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (i : ShannonIndex theta n) :
    effectiveVelocity (shannonLineData theta n z) 0 i =
      shannonVelocity theta n z i := by
  simp [effectiveVelocity, shannonLineData]

theorem shannonLineSlope_zero_add (theta : ShannonData) (n : ℕ)
    (z w : ℝ × ℝ) :
    letI := shannonIndexNonempty theta n
    shannonLineSlope (shannonLineData theta n (z + w)) 0 =
      shannonLineSlope (shannonLineData theta n z) 0 +
        shannonLineSlope (shannonLineData theta n w) 0 := by
  letI := shannonIndexNonempty theta n
  unfold shannonLineSlope
  simp_rw [lineProb_shannonLine_zero_apply_parameter_independent
      theta n (z + w) z,
    lineProb_shannonLine_zero_apply_parameter_independent theta n w z,
    effectiveVelocity_shannonLine_zero,
    escortMean_shannonLine_zero, shannonMean_add, shannonVelocity_add]
  calc
    -∑ i, (lineProb (shannonLineData theta n z) 0).1 i *
          (shannonVelocity theta n z i + shannonVelocity theta n w i -
            (shannonMean theta n z 1 + shannonMean theta n w 1)) *
            Real.log ((lineProb (shannonLineData theta n z) 0).1 i) =
        -∑ i, ((lineProb (shannonLineData theta n z) 0).1 i *
            (shannonVelocity theta n z i - shannonMean theta n z 1) *
              Real.log ((lineProb (shannonLineData theta n z) 0).1 i) +
          (lineProb (shannonLineData theta n z) 0).1 i *
            (shannonVelocity theta n w i - shannonMean theta n w 1) *
              Real.log ((lineProb (shannonLineData theta n z) 0).1 i)) := by
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = _ := by rw [Finset.sum_add_distrib]; ring

theorem shannonLineSlope_zero_smul (theta : ShannonData) (n : ℕ)
    (c : ℝ) (z : ℝ × ℝ) :
    letI := shannonIndexNonempty theta n
    shannonLineSlope (shannonLineData theta n (c • z)) 0 =
      c * shannonLineSlope (shannonLineData theta n z) 0 := by
  letI := shannonIndexNonempty theta n
  unfold shannonLineSlope
  simp_rw [lineProb_shannonLine_zero_apply_parameter_independent
      theta n (c • z) z,
    effectiveVelocity_shannonLine_zero,
    escortMean_shannonLine_zero, shannonMean_smul, shannonVelocity_smul]
  calc
    -∑ i, (lineProb (shannonLineData theta n z) 0).1 i *
          (c * shannonVelocity theta n z i -
            c * shannonMean theta n z 1) *
            Real.log ((lineProb (shannonLineData theta n z) 0).1 i) =
        -∑ i, c * ((lineProb (shannonLineData theta n z) 0).1 i *
          (shannonVelocity theta n z i - shannonMean theta n z 1) *
            Real.log ((lineProb (shannonLineData theta n z) 0).1 i)) := by
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem continuous_shannonLineSlope_zero (theta : ShannonData) (n : ℕ) :
    letI := shannonIndexNonempty theta n
    Continuous (fun z : ℝ × ℝ ↦
      shannonLineSlope (shannonLineData theta n z) 0) := by
  letI := shannonIndexNonempty theta n
  let z0 : ℝ × ℝ := (0, 0)
  let P := lineProb (shannonLineData theta n z0) 0
  have heq : (fun z : ℝ × ℝ ↦
      shannonLineSlope (shannonLineData theta n z) 0) =
      fun z ↦ -∑ i, P.1 i *
        (shannonVelocity theta n z i - shannonMean theta n z 1) *
          Real.log (P.1 i) := by
    funext z
    unfold shannonLineSlope
    simp_rw [lineProb_shannonLine_zero_apply_parameter_independent theta n z z0,
      effectiveVelocity_shannonLine_zero,
      escortMean_shannonLine_zero]
    rfl
  rw [heq]
  apply Continuous.neg
  apply continuous_finsetSum
  intro i _hi
  have hvel : Continuous (fun z : ℝ × ℝ ↦ shannonVelocity theta n z i) := by
    unfold shannonVelocity
    fun_prop
  exact (continuous_const.mul
    (hvel.sub (continuous_shannonMean theta n 1))).mul continuous_const

theorem shannonKOne_add (theta : ShannonData) (n : ℕ)
    (z w : ℝ × ℝ) (beta : Param) :
    shannonKOne theta n (z + w) beta =
      shannonKOne theta n z beta + shannonKOne theta n w beta := by
  letI := shannonIndexNonempty theta n
  unfold shannonKOne
  by_cases hzero : beta = 0
  · subst beta
    simp only [entropyLineFirst_zero _ (linePositiveZero _), add_zero]
  by_cases hone : beta = 1
  · subst beta
    rw [entropyLineFirst_one _ (linePositiveZero _),
      entropyLineFirst_one _ (linePositiveZero _),
      entropyLineFirst_one _ (linePositiveZero _),
      shannonLineSlope_zero_add]
  by_cases htop : beta = ⊤
  · subst beta
    obtain ⟨ezw, hezw, hfixedzw⟩ :=
      exists_fixedMaxCoordinate_shannonLine theta n (z + w)
    obtain ⟨ez, hez, hfixedz⟩ :=
      exists_fixedMaxCoordinate_shannonLine theta n z
    obtain ⟨ew, hew, hfixedw⟩ :=
      exists_fixedMaxCoordinate_shannonLine theta n w
    have hzw0 : (0 : ℝ) ∈ Ioo (-ezw) ezw := by constructor <;> linarith
    have hz0 : (0 : ℝ) ∈ Ioo (-ez) ez := by constructor <;> linarith
    have hw0 : (0 : ℝ) ∈ Ioo (-ew) ew := by constructor <;> linarith
    rw [entropyLineFirst_top_on _ isOpen_Ioo hfixedzw hzw0,
      entropyLineFirst_top_on _ isOpen_Ioo hfixedz hz0,
      entropyLineFirst_top_on _ isOpen_Ioo hfixedw hw0,
      escortMean_shannonLine_zero, escortMean_shannonLine_zero,
      escortMean_shannonLine_zero, shannonMean_add,
      effectiveVelocity_shannonLine_zero,
      effectiveVelocity_shannonLine_zero,
      effectiveVelocity_shannonLine_zero,
      shannonVelocity_add]
    ring
  let a := ENNReal.toReal beta
  have ha : finiteParam a = beta := finiteParam_paramToReal beta htop
  have ha0 : 0 < a := ENNReal.toReal_pos hzero htop
  have ha1 : a ≠ 1 := by
    intro haone
    apply hone
    rw [← ha, haone, finiteParam_one]
  rw [← ha, entropyLineFirst_finite_zero _ ha0 ha1,
    entropyLineFirst_finite_zero _ ha0 ha1,
    entropyLineFirst_finite_zero _ ha0 ha1,
    escortMean_shannonLine_zero, escortMean_shannonLine_zero,
    escortMean_shannonLine_zero, escortMean_shannonLine_zero,
    escortMean_shannonLine_zero, escortMean_shannonLine_zero,
    shannonMean_add theta n z w a, shannonMean_add theta n z w 1]
  ring

theorem shannonKOne_smul (theta : ShannonData) (n : ℕ)
    (c : ℝ) (z : ℝ × ℝ) (beta : Param) :
    shannonKOne theta n (c • z) beta = c * shannonKOne theta n z beta := by
  letI := shannonIndexNonempty theta n
  unfold shannonKOne
  by_cases hzero : beta = 0
  · subst beta
    simp only [entropyLineFirst_zero _ (linePositiveZero _), mul_zero]
  by_cases hone : beta = 1
  · subst beta
    rw [entropyLineFirst_one _ (linePositiveZero _),
      entropyLineFirst_one _ (linePositiveZero _),
      shannonLineSlope_zero_smul]
  by_cases htop : beta = ⊤
  · subst beta
    obtain ⟨ecz, hecz, hfixedcz⟩ :=
      exists_fixedMaxCoordinate_shannonLine theta n (c • z)
    obtain ⟨ez, hez, hfixedz⟩ :=
      exists_fixedMaxCoordinate_shannonLine theta n z
    have hcz0 : (0 : ℝ) ∈ Ioo (-ecz) ecz := by constructor <;> linarith
    have hz0 : (0 : ℝ) ∈ Ioo (-ez) ez := by constructor <;> linarith
    rw [entropyLineFirst_top_on _ isOpen_Ioo hfixedcz hcz0,
      entropyLineFirst_top_on _ isOpen_Ioo hfixedz hz0,
      escortMean_shannonLine_zero, escortMean_shannonLine_zero,
      shannonMean_smul, effectiveVelocity_shannonLine_zero,
      effectiveVelocity_shannonLine_zero, shannonVelocity_smul]
    ring
  let a := ENNReal.toReal beta
  have ha : finiteParam a = beta := finiteParam_paramToReal beta htop
  have ha0 : 0 < a := ENNReal.toReal_pos hzero htop
  have ha1 : a ≠ 1 := by
    intro haone
    apply hone
    rw [← ha, haone, finiteParam_one]
  rw [← ha, entropyLineFirst_finite_zero _ ha0 ha1,
    entropyLineFirst_finite_zero _ ha0 ha1,
    escortMean_shannonLine_zero, escortMean_shannonLine_zero,
    escortMean_shannonLine_zero, escortMean_shannonLine_zero,
    shannonMean_smul, shannonMean_smul]
  ring

/-- First coordinate basis vector for the Shannon velocity plane. -/
def shannonBasisOne : ℝ × ℝ := (1, 0)

/-- Second coordinate basis vector for the Shannon velocity plane. -/
def shannonBasisTwo : ℝ × ℝ := (0, 1)

theorem shannonBasisDecomposition (z : ℝ × ℝ) :
    z = z.1 • shannonBasisOne + z.2 • shannonBasisTwo := by
  ext <;> simp [shannonBasisOne, shannonBasisTwo]

/-- Polarized second escort moment, with weights fixed at the common Shannon
base point. -/
def shannonCross (theta : ShannonData) (n : ℕ) (z w : ℝ × ℝ)
    (alpha : ℝ) : ℝ :=
  ∑ j : Fin 3, shannonEscort theta n (0, 0) j alpha *
    shannonBlockVelocity theta n z j * shannonBlockVelocity theta n w j

private theorem shannonSecond_eq_fixed_sum (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    shannonSecond theta n z alpha =
      ∑ j : Fin 3, shannonEscort theta n (0, 0) j alpha *
        shannonBlockVelocity theta n z j ^ 2 := by
  unfold shannonSecond
  apply Finset.sum_congr rfl
  intro j _hj
  rw [shannonEscort_parameter_independent theta n z (0, 0)]

theorem shannonSecond_add (theta : ShannonData) (n : ℕ)
    (z w : ℝ × ℝ) (alpha : ℝ) :
    shannonSecond theta n (z + w) alpha =
      shannonSecond theta n z alpha + 2 * shannonCross theta n z w alpha +
        shannonSecond theta n w alpha := by
  rw [shannonSecond_eq_fixed_sum, shannonSecond_eq_fixed_sum,
    shannonSecond_eq_fixed_sum]
  unfold shannonCross
  calc
    ∑ j, shannonEscort theta n (0, 0) j alpha *
          shannonBlockVelocity theta n (z + w) j ^ 2 =
        ∑ j, (shannonEscort theta n (0, 0) j alpha *
            shannonBlockVelocity theta n z j ^ 2 +
          2 * (shannonEscort theta n (0, 0) j alpha *
            shannonBlockVelocity theta n z j *
              shannonBlockVelocity theta n w j) +
          shannonEscort theta n (0, 0) j alpha *
            shannonBlockVelocity theta n w j ^ 2) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [shannonBlockVelocity_add]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.mul_sum]

theorem shannonSecond_smul (theta : ShannonData) (n : ℕ)
    (c : ℝ) (z : ℝ × ℝ) (alpha : ℝ) :
    shannonSecond theta n (c • z) alpha =
      c ^ 2 * shannonSecond theta n z alpha := by
  rw [shannonSecond_eq_fixed_sum, shannonSecond_eq_fixed_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [shannonBlockVelocity_smul]
  ring

theorem shannonCross_smul_left (theta : ShannonData) (n : ℕ)
    (c : ℝ) (z w : ℝ × ℝ) (alpha : ℝ) :
    shannonCross theta n (c • z) w alpha =
      c * shannonCross theta n z w alpha := by
  unfold shannonCross
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [shannonBlockVelocity_smul]
  ring

theorem shannonCross_smul_right (theta : ShannonData) (n : ℕ)
    (c : ℝ) (z w : ℝ × ℝ) (alpha : ℝ) :
    shannonCross theta n z (c • w) alpha =
      c * shannonCross theta n z w alpha := by
  unfold shannonCross
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [shannonBlockVelocity_smul]
  ring

theorem shannonSecond_basis_decomposition (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    shannonSecond theta n z alpha =
      z.1 ^ 2 * shannonSecond theta n shannonBasisOne alpha +
      z.1 * z.2 *
        (shannonSecond theta n (shannonBasisOne + shannonBasisTwo) alpha -
          shannonSecond theta n shannonBasisOne alpha -
          shannonSecond theta n shannonBasisTwo alpha) +
      z.2 ^ 2 * shannonSecond theta n shannonBasisTwo alpha := by
  conv_lhs => rw [shannonBasisDecomposition z]
  rw [shannonSecond_add, shannonSecond_smul, shannonSecond_smul,
    shannonCross_smul_left, shannonCross_smul_right]
  have h12 := shannonSecond_add theta n shannonBasisOne shannonBasisTwo alpha
  rw [h12]
  ring

theorem shannonMean_basis_decomposition (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    shannonMean theta n z alpha =
      z.1 * shannonMean theta n shannonBasisOne alpha +
        z.2 * shannonMean theta n shannonBasisTwo alpha := by
  conv_lhs => rw [shannonBasisDecomposition z]
  rw [shannonMean_add, shannonMean_smul, shannonMean_smul]

theorem shannonSlope_basis_decomposition (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) :
    letI := shannonIndexNonempty theta n
    shannonLineSlope (shannonLineData theta n z) 0 =
      z.1 * shannonLineSlope
        (shannonLineData theta n shannonBasisOne) 0 +
      z.2 * shannonLineSlope
        (shannonLineData theta n shannonBasisTwo) 0 := by
  letI := shannonIndexNonempty theta n
  conv_lhs => rw [shannonBasisDecomposition z]
  rw [shannonLineSlope_zero_add, shannonLineSlope_zero_smul,
    shannonLineSlope_zero_smul]

@[simp] theorem shannonKTwo_zero (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) : shannonKTwo theta n z 0 = 0 := by
  letI := shannonIndexNonempty theta n
  unfold shannonKTwo
  exact entropyLineSecond_zero _ (linePositiveZero _)

theorem shannonKTwo_one (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) :
    letI := shannonIndexNonempty theta n
    shannonKTwo theta n z 1 =
      -shannonVar theta n z 1 -
        2 * shannonMean theta n z 1 *
          shannonLineSlope (shannonLineData theta n z) 0 := by
  letI := shannonIndexNonempty theta n
  unfold shannonKTwo
  rw [entropyLineSecond_one _ (linePositiveZero _),
    escortVar_shannonLine_zero, escortMean_shannonLine_zero]

theorem shannonKTwo_finite (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) :
    shannonKTwo theta n z (finiteParam a) =
      -a * shannonVar theta n z a +
        singularWeight (finiteParam a) *
          (shannonMean theta n z 1 ^ 2 - shannonMean theta n z a ^ 2) := by
  letI := shannonIndexNonempty theta n
  unfold shannonKTwo
  rw [entropyLineSecond_finite_zero _ ha ha1,
    escortVar_shannonLine_zero, escortMean_shannonLine_zero,
    escortMean_shannonLine_zero]

theorem shannonKTwo_top (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) :
    shannonKTwo theta n z ⊤ =
      z.2 ^ 2 - shannonMean theta n z 1 ^ 2 := by
  letI := shannonIndexNonempty theta n
  unfold shannonKTwo
  obtain ⟨epsilon, hepsilon, hfixed⟩ :=
    exists_fixedMaxCoordinate_shannonLine theta n z
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := by
    constructor <;> linarith
  rw [entropyLineSecond_top_on _ isOpen_Ioo hfixed hzero,
    effectiveVelocity_shannonLine_zero, escortMean_shannonLine_zero]
  rfl

theorem shannonKTwo_basis_decomposition (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (beta : Param) :
    shannonKTwo theta n z beta =
      z.1 ^ 2 * shannonKTwo theta n shannonBasisOne beta +
      z.1 * z.2 *
        (shannonKTwo theta n (shannonBasisOne + shannonBasisTwo) beta -
          shannonKTwo theta n shannonBasisOne beta -
          shannonKTwo theta n shannonBasisTwo beta) +
      z.2 ^ 2 * shannonKTwo theta n shannonBasisTwo beta := by
  letI := shannonIndexNonempty theta n
  by_cases hzero : beta = 0
  · subst beta
    simp
  by_cases hone : beta = 1
  · subst beta
    simp_rw [shannonKTwo_one]
    unfold shannonVar
    rw [shannonSecond_basis_decomposition theta n z 1,
      shannonMean_basis_decomposition theta n z 1,
      shannonSlope_basis_decomposition theta n z,
      shannonMean_basis_decomposition theta n
        (shannonBasisOne + shannonBasisTwo) 1,
      shannonSlope_basis_decomposition theta n
        (shannonBasisOne + shannonBasisTwo)]
    simp only [shannonBasisOne, shannonBasisTwo, Prod.fst_add, Prod.snd_add]
    ring
  by_cases htop : beta = ⊤
  · subst beta
    simp_rw [shannonKTwo_top]
    rw [shannonMean_basis_decomposition theta n z 1,
      shannonMean_basis_decomposition theta n
        (shannonBasisOne + shannonBasisTwo) 1]
    simp [shannonBasisOne, shannonBasisTwo]
    ring
  let a := ENNReal.toReal beta
  have ha : finiteParam a = beta := finiteParam_paramToReal beta htop
  have ha0 : 0 < a := ENNReal.toReal_pos hzero htop
  have ha1 : a ≠ 1 := by
    intro haone
    apply hone
    rw [← ha, haone, finiteParam_one]
  rw [← ha]
  simp_rw [shannonKTwo_finite _ _ _ ha0 ha1]
  unfold shannonVar
  rw [shannonSecond_basis_decomposition theta n z a,
    shannonMean_basis_decomposition theta n z a,
    shannonMean_basis_decomposition theta n z 1,
    shannonMean_basis_decomposition theta n
      (shannonBasisOne + shannonBasisTwo) a,
    shannonMean_basis_decomposition theta n
      (shannonBasisOne + shannonBasisTwo) 1]
  simp only [shannonBasisOne, shannonBasisTwo, Prod.fst_add, Prod.snd_add]
  ring

end ConditionalEntropy
