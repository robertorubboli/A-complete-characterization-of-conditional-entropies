import ConditionalEntropy.BlockCurves

/-!
# The three-block Shannon localization family

This module fixes the dependent carrier, the multiplicative line, its
blockwise escorts, and all scalar kernels used to localize a signed parameter
measure at Renyi order one.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

/-- Parameters of the dedicated three-block Shannon perturbation. -/
structure ShannonData where
  c : ℝ
  R : ℝ
  p : ℝ
  c_gt_one : 1 < c
  R_gt : c + 1 < R
  p_pos : 0 < p
  p_lt_one : p < 1

namespace ShannonData

/-- Complementary probability weight. -/
def q (theta : ShannonData) : ℝ := 1 - theta.p

theorem q_pos (theta : ShannonData) : 0 < theta.q := by
  exact sub_pos.mpr theta.p_lt_one

theorem q_lt_one (theta : ShannonData) : theta.q < 1 := by
  unfold q
  linarith [theta.p_pos]

end ShannonData

/-- Natural scale of the Shannon construction. -/
def shannonScale (n : ℕ) : ℝ := blockScale n

/-- Logarithm of the Shannon scale. -/
def shannonLogScale (n : ℕ) : ℝ := Real.log (shannonScale n)

theorem shannonScale_pos (n : ℕ) : 0 < shannonScale n :=
  blockScale_pos n

theorem one_lt_shannonScale (n : ℕ) : 1 < shannonScale n := by
  unfold shannonScale blockScale
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem shannonLogScale_pos (n : ℕ) : 0 < shannonLogScale n := by
  exact Real.log_pos (one_lt_shannonScale n)

/-- Rounded cardinalities of the three Shannon blocks. -/
def shannonCount (theta : ShannonData) (n : ℕ) : Fin 3 → ℕ :=
  ![Nat.ceil (Real.rpow (shannonScale n) theta.R),
    Nat.ceil (Real.rpow (shannonScale n) (theta.R - 1)),
    Nat.ceil (Real.rpow (shannonScale n) (theta.R - 1 - theta.c))]

/-- Dependent finite carrier of the Shannon blocks. -/
abbrev ShannonIndex (theta : ShannonData) (n : ℕ) :=
  Σ j : Fin 3, Fin (shannonCount theta n j)

theorem shannonCount_pos (theta : ShannonData) (n : ℕ) (j : Fin 3) :
    0 < shannonCount theta n j := by
  fin_cases j
  · change 0 < Nat.ceil (Real.rpow (shannonScale n) theta.R)
    rw [Nat.ceil_pos]
    exact Real.rpow_pos_of_pos (shannonScale_pos n) _
  · change 0 < Nat.ceil (Real.rpow (shannonScale n) (theta.R - 1))
    rw [Nat.ceil_pos]
    exact Real.rpow_pos_of_pos (shannonScale_pos n) _
  · change 0 < Nat.ceil
      (Real.rpow (shannonScale n) (theta.R - 1 - theta.c))
    rw [Nat.ceil_pos]
    exact Real.rpow_pos_of_pos (shannonScale_pos n) _

/-- Explicit nonempty witness for the dependent Shannon carrier. -/
theorem shannonIndexNonempty (theta : ShannonData) (n : ℕ) :
    Nonempty (ShannonIndex theta n) :=
  ⟨⟨0, ⟨0, shannonCount_pos theta n 0⟩⟩⟩

/-- A canonical coordinate in each nonempty Shannon block. -/
def shannonRepresentative (theta : ShannonData) (n : ℕ) (j : Fin 3) :
    ShannonIndex theta n :=
  ⟨j, ⟨0, shannonCount_pos theta n j⟩⟩

/-- Positive base values, constant on the three Shannon blocks. -/
def shannonBase (theta : ShannonData) (n : ℕ) (_z : ℝ × ℝ) :
    ShannonIndex theta n → ℝ :=
  fun i ↦ ![theta.q, shannonScale n * theta.p, shannonScale n ^ 2] i.1

/-- Blockwise multiplicative velocity. -/
def shannonVelocity (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) :
    ShannonIndex theta n → ℝ :=
  fun i ↦ ![z.1 / (theta.q * shannonLogScale n),
    -z.1 / (theta.p * shannonLogScale n), z.2] i.1

theorem shannonBase_pos (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (i : ShannonIndex theta n) : 0 < shannonBase theta n z i := by
  rcases i with ⟨j, hj⟩
  fin_cases j
  · change 0 < theta.q
    exact theta.q_pos
  · change 0 < shannonScale n * theta.p
    exact mul_pos (shannonScale_pos n) theta.p_pos
  · change 0 < shannonScale n ^ 2
    exact pow_pos (shannonScale_pos n) 2

/-- Positive line data of the Shannon perturbation. -/
def shannonLineData (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) :
    PositiveLineData (ShannonIndex theta n) where
  x := shannonBase theta n z
  u := shannonVelocity theta n z
  x_pos := shannonBase_pos theta n z

/-- Raw coordinates along the Shannon multiplicative line. -/
def shannonLineRaw (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (lambda : ℝ) : ShannonIndex theta n → ℝ :=
  lineRaw (shannonLineData theta n z) lambda

@[simp] theorem shannonLineRaw_apply (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (lambda : ℝ) (i : ShannonIndex theta n) :
    shannonLineRaw theta n z lambda i =
      shannonBase theta n z i * (1 + shannonVelocity theta n z i * lambda) :=
  rfl

/-- Total (unnormalized) mass of the Shannon line. -/
def shannonMass (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (lambda : ℝ) : ℝ :=
  ∑ i : ShannonIndex theta n, shannonLineRaw theta n z lambda i

/-- Normalized mass carried by an entire Shannon block. -/
def shannonBlockMass (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (j : Fin 3) (lambda : ℝ) : ℝ :=
  (shannonCount theta n j : ℝ) *
      shannonLineRaw theta n z lambda (shannonRepresentative theta n j) /
    shannonMass theta n z lambda

/-- Power-sum contribution of one Shannon block. -/
def shannonContribution (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (j : Fin 3) (alpha : ℝ) : ℝ :=
  (shannonCount theta n j : ℝ) *
    Real.rpow (shannonBase theta n z (shannonRepresentative theta n j)) alpha

/-- Escort mass carried by one Shannon block. -/
def shannonEscort (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (j : Fin 3) (alpha : ℝ) : ℝ :=
  shannonContribution theta n z j alpha /
    ∑ l : Fin 3, shannonContribution theta n z l alpha

/-- Velocity of a Shannon block. -/
def shannonBlockVelocity (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (j : Fin 3) : ℝ :=
  shannonVelocity theta n z (shannonRepresentative theta n j)

/-- Logarithm of a Shannon block base value. -/
def shannonLogBase (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (j : Fin 3) : ℝ :=
  Real.log (shannonBase theta n z (shannonRepresentative theta n j))

/-- Escort average of block log-base values. -/
def shannonEscortLogMean (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (alpha : ℝ) : ℝ :=
  ∑ j : Fin 3, shannonEscort theta n z j alpha * shannonLogBase theta n z j

/-- Escort mean of the Shannon block velocities. -/
def shannonMean (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (alpha : ℝ) : ℝ :=
  ∑ j : Fin 3,
    shannonEscort theta n z j alpha * shannonBlockVelocity theta n z j

/-- Escort second moment of the Shannon block velocities. -/
def shannonSecond (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (alpha : ℝ) : ℝ :=
  ∑ j : Fin 3,
    shannonEscort theta n z j alpha * shannonBlockVelocity theta n z j ^ 2

/-- Escort variance of the Shannon block velocities. -/
def shannonVar (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (alpha : ℝ) : ℝ :=
  shannonSecond theta n z alpha - shannonMean theta n z alpha ^ 2

/-- The third Shannon block is strictly largest at the base point. -/
theorem shannonTopUniqueAtZero (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) :
    ∀ i : ShannonIndex theta n, i.1 ≠ 2 →
      shannonLineRaw theta n z 0 i <
        shannonLineRaw theta n z 0 (shannonRepresentative theta n 2) := by
  intro i hi
  rcases i with ⟨j, hj⟩
  fin_cases j
  · have hd2 : 1 < shannonScale n ^ 2 := by
      have hd := one_lt_shannonScale n
      nlinarith [sq_nonneg (shannonScale n - 1)]
    simpa [shannonLineRaw, shannonLineData, lineRaw, shannonBase,
      shannonRepresentative] using theta.q_lt_one.trans hd2
  · have hlt : shannonScale n * theta.p < shannonScale n ^ 2 := by
      calc
        shannonScale n * theta.p < shannonScale n * shannonScale n :=
          mul_lt_mul_of_pos_left (theta.p_lt_one.trans (one_lt_shannonScale n))
            (shannonScale_pos n)
        _ = shannonScale n ^ 2 := by ring
    simpa [shannonLineRaw, shannonLineData, lineRaw, shannonBase,
      shannonRepresentative] using hlt
  · exact (hi rfl).elim

/-- First entropy derivative kernel at the Shannon base point. -/
def shannonKOne (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (beta : Param) : ℝ := by
  letI := shannonIndexNonempty theta n
  exact entropyLineFirst (shannonLineData theta n z) beta 0

/-- Second entropy derivative kernel at the Shannon base point. -/
def shannonKTwo (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (beta : Param) : ℝ := by
  letI := shannonIndexNonempty theta n
  exact entropyLineSecond (shannonLineData theta n z) beta 0

/-- Logarithmic signed-column derivative kernel. -/
def shannonLogKernel (mu : SignedMeasure Param) (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (q : ℕ) : ℝ := by
  letI := shannonIndexNonempty theta n
  exact iteratedDeriv (signedLogPhiLine mu (shannonLineData theta n z)) q 0

/-- Norm-free integrated-entropy derivative kernel. -/
def shannonGKernel (mu : SignedMeasure Param) (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (q : ℕ) : ℝ := by
  letI := shannonIndexNonempty theta n
  exact iteratedDeriv (integratedEntropyLine mu (shannonLineData theta n z)) q 0

/-- Derivatives of the logarithm of the raw Shannon mass. -/
def shannonLogMassKernel (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (q : ℕ) : ℝ :=
  iteratedDeriv (fun lambda ↦ Real.log (shannonMass theta n z lambda)) q 0

/-- Total signed exponential column curve of the Shannon line. -/
def shannonPhiCurve (mu : SignedMeasure Param) (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (lambda : ℝ) : ℝ := by
  letI := shannonIndexNonempty theta n
  exact PhiSigned mu (lineConeTotal (shannonLineData theta n z) lambda)

/-- Total norm-free signed entropy curve of the Shannon line. -/
def shannonGCurve (mu : SignedMeasure Param) (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (lambda : ℝ) : ℝ := by
  letI := shannonIndexNonempty theta n
  exact GSigned mu (linePosConeTotal (shannonLineData theta n z) lambda)

end ConditionalEntropy
