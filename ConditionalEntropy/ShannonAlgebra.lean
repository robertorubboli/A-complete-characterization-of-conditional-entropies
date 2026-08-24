import ConditionalEntropy.ShannonData

/-!
# Finite algebra for the Shannon localization line

The lemmas here reduce all coordinate sums to the three named blocks and
construct the fixed maximal coordinate required by the endpoint derivative
formulas.  The explicit Shannon main term and its uniform `C²` error are also
fixed here.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

theorem shannonBase_eq_blockRepresentative (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (i : ShannonIndex theta n) :
    shannonBase theta n z i =
      shannonBase theta n z (shannonRepresentative theta n i.1) := by
  rfl

theorem shannonVelocity_eq_blockRepresentative (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (i : ShannonIndex theta n) :
    shannonVelocity theta n z i = shannonBlockVelocity theta n z i.1 := by
  rfl

theorem shannonContribution_pos (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (j : Fin 3) (alpha : ℝ) :
    0 < shannonContribution theta n z j alpha := by
  apply mul_pos
  · exact_mod_cast shannonCount_pos theta n j
  · exact Real.rpow_pos_of_pos
      (shannonBase_pos theta n z (shannonRepresentative theta n j)) alpha

theorem sum_shannonContribution_pos (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    0 < ∑ j : Fin 3, shannonContribution theta n z j alpha := by
  exact Finset.sum_pos
    (fun j _ ↦ shannonContribution_pos theta n z j alpha)
    Finset.univ_nonempty

theorem shannonEscort_nonneg (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (j : Fin 3) (alpha : ℝ) :
    0 ≤ shannonEscort theta n z j alpha :=
  (div_pos (shannonContribution_pos theta n z j alpha)
    (sum_shannonContribution_pos theta n z alpha)).le

theorem sum_shannonEscort (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    ∑ j : Fin 3, shannonEscort theta n z j alpha = 1 := by
  unfold shannonEscort
  rw [← Finset.sum_div]
  exact div_self (sum_shannonContribution_pos theta n z alpha).ne'

/-- Power sums of the coordinate base decompose into the three declared
block contributions. -/
theorem sum_rpow_shannonBase_eq_contributions (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    ∑ i : ShannonIndex theta n, Real.rpow (shannonBase theta n z i) alpha =
      ∑ j : Fin 3, shannonContribution theta n z j alpha := by
  change (∑ i : Σ j : Fin 3, Fin (shannonCount theta n j),
      Real.rpow (shannonBase theta n z i) alpha) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ _i : Fin (shannonCount theta n j),
      Real.rpow
        (shannonBase theta n z (shannonRepresentative theta n j)) alpha) = _
  simp [shannonContribution]

/-- A coordinate escort sum over one block is its block escort. -/
theorem sum_escortWeight_shannon_zero (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) (j : Fin 3) :
    ∑ i : Fin (shannonCount theta n j),
      escortWeight (shannonLineData theta n z) alpha 0 ⟨j, i⟩ =
        shannonEscort theta n z j alpha := by
  simp only [escortWeight, lineRaw, shannonLineData, mul_zero, add_zero, mul_one]
  calc
    (∑ i : Fin (shannonCount theta n j),
        Real.rpow (shannonBase theta n z ⟨j, i⟩) alpha /
          (∑ x : ShannonIndex theta n,
            Real.rpow (shannonBase theta n z x) alpha)) =
      ∑ _i : Fin (shannonCount theta n j),
        Real.rpow
            (shannonBase theta n z (shannonRepresentative theta n j)) alpha /
          (∑ x : ShannonIndex theta n,
            Real.rpow (shannonBase theta n z x) alpha) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [shannonBase_eq_blockRepresentative]
    _ = ∑ _i : Fin (shannonCount theta n j),
        Real.rpow
            (shannonBase theta n z (shannonRepresentative theta n j)) alpha /
          (∑ l : Fin 3, shannonContribution theta n z l alpha) := by
              rw [sum_rpow_shannonBase_eq_contributions]
    _ = shannonEscort theta n z j alpha := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      unfold shannonEscort shannonContribution
      ring

theorem sum_escortWeight_mul_shannonValue (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) (v : Fin 3 → ℝ) :
    ∑ i : ShannonIndex theta n,
      escortWeight (shannonLineData theta n z) alpha 0 i * v i.1 =
        ∑ j : Fin 3, shannonEscort theta n z j alpha * v j := by
  change (∑ i : Σ j : Fin 3, Fin (shannonCount theta n j),
      escortWeight (shannonLineData theta n z) alpha 0 i * v i.1) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ i ∈ Finset.univ,
    escortWeight (shannonLineData theta n z) alpha 0 ⟨j, i⟩ * v j) = _
  rw [← Finset.sum_mul, sum_escortWeight_shannon_zero]

theorem escortMean_shannonLine_zero (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    escortMean (shannonLineData theta n z) alpha 0 =
      shannonMean theta n z alpha := by
  simpa only [escortMean, effectiveVelocity, shannonMean, shannonLineData,
    mul_zero, add_zero, div_one, shannonVelocity_eq_blockRepresentative] using
    sum_escortWeight_mul_shannonValue theta n z alpha
      (fun j ↦ shannonBlockVelocity theta n z j)

theorem escortSecond_shannonLine_zero (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    escortSecond (shannonLineData theta n z) alpha 0 =
      shannonSecond theta n z alpha := by
  simpa only [escortSecond, effectiveVelocity, shannonSecond, shannonLineData,
    mul_zero, add_zero, div_one, shannonVelocity_eq_blockRepresentative] using
    sum_escortWeight_mul_shannonValue theta n z alpha
      (fun j ↦ shannonBlockVelocity theta n z j ^ 2)

theorem escortVar_shannonLine_zero (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (alpha : ℝ) :
    escortVar (shannonLineData theta n z) alpha 0 =
      shannonVar theta n z alpha := by
  rw [escortVar, shannonVar, escortMean_shannonLine_zero,
    escortSecond_shannonLine_zero]

@[simp] theorem shannonBlockVelocity_zero (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) :
    shannonBlockVelocity theta n z 0 =
      z.1 / (theta.q * shannonLogScale n) := by
  rfl

@[simp] theorem shannonBlockVelocity_one (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) :
    shannonBlockVelocity theta n z 1 =
      -z.1 / (theta.p * shannonLogScale n) := by
  rfl

@[simp] theorem shannonBlockVelocity_two (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) :
    shannonBlockVelocity theta n z 2 = z.2 := by
  rfl

/-- Strict maximality at zero persists on a symmetric interval, including
the identical-velocity tie condition within the third block. -/
theorem exists_fixedMaxCoordinate_shannonLine (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      FixedMaxCoordinate (shannonLineData theta n z) (Ioo (-epsilon) epsilon)
        (shannonRepresentative theta n 2) := by
  let L := shannonLineData theta n z
  let istar := shannonRepresentative theta n 2
  have hposEventually :
      ∀ᶠ lambda in nhds (0 : ℝ), ∀ i : ShannonIndex theta n,
        0 < lineRaw L lambda i := by
    rw [Filter.eventually_all]
    intro i
    have hcont : ContinuousAt (fun lambda ↦ lineRaw L lambda i) 0 :=
      (hasDerivAt_lineRaw L 0 i).continuousAt
    exact continuousAt_const.eventually_lt hcont (by
      dsimp only [L]
      exact linePositiveZero (shannonLineData theta n z) i)
  have hmaxEventually :
      ∀ᶠ lambda in nhds (0 : ℝ), ∀ i : ShannonIndex theta n,
        i.1 ≠ 2 → lineRaw L lambda i < lineRaw L lambda istar := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i.1 = 2
    · exact Filter.Eventually.of_forall fun _ hne ↦ (hne hi).elim
    · have hconti : ContinuousAt (fun lambda ↦ lineRaw L lambda i) 0 :=
        (hasDerivAt_lineRaw L 0 i).continuousAt
      have hcontstar : ContinuousAt (fun lambda ↦ lineRaw L lambda istar) 0 :=
        (hasDerivAt_lineRaw L 0 istar).continuousAt
      have hbase : lineRaw L 0 i < lineRaw L 0 istar := by
        dsimp only [L, istar]
        exact shannonTopUniqueAtZero theta n z i hi
      exact (hconti.eventually_lt hcontstar hbase).mono
        (fun _ hlt _ ↦ hlt)
  obtain ⟨lo, hi, hlohi, hsubset⟩ :=
    (hposEventually.and hmaxEventually).exists_Ioo_subset
  let epsilon := min (-lo) hi
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    exact lt_min (neg_pos.mpr hlohi.1) hlohi.2
  refine ⟨epsilon, hepsilon, ?_⟩
  intro lambda hlambda
  have hgood :
      (∀ i : ShannonIndex theta n, 0 < lineRaw L lambda i) ∧
      (∀ i : ShannonIndex theta n,
        i.1 ≠ 2 → lineRaw L lambda i < lineRaw L lambda istar) := by
    apply hsubset
    constructor
    · exact lt_of_le_of_lt (by
        dsimp only [epsilon]
        linarith [min_le_left (-lo) hi]) hlambda.1
    · exact hlambda.2.trans_le (by
        dsimp only [epsilon]
        exact min_le_right (-lo) hi)
  refine ⟨?_, ?_, ?_⟩
  · change ∀ i : ShannonIndex theta n,
      0 < lineRaw (shannonLineData theta n z) lambda i
    simpa only [L] using hgood.1
  · intro i
    by_cases hiBlock : i.1 = 2
    · have heq : lineRaw L lambda i = lineRaw L lambda istar := by
        rcases i with ⟨j, hj⟩
        change j = 2 at hiBlock
        subst j
        rfl
      exact heq.le
    · exact (hgood.2 i hiBlock).le
  · intro i heq
    by_cases hiBlock : i.1 = 2
    · rcases i with ⟨j, hj⟩
      change j = 2 at hiBlock
      subst j
      rfl
    · exact ((ne_of_lt (hgood.2 i hiBlock)) heq).elim

/-- Explicit leading Shannon entropy term. -/
def shannonMain (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (lambda : ℝ) : ℝ :=
  (theta.R - theta.p + z.1 * lambda / shannonLogScale n) *
      shannonLogScale n -
    (theta.q + z.1 * lambda / shannonLogScale n) *
      Real.log (theta.q + z.1 * lambda / shannonLogScale n) -
    (theta.p - z.1 * lambda / shannonLogScale n) *
      Real.log (theta.p - z.1 * lambda / shannonLogScale n)

/-- Difference between the exact Shannon entropy and its explicit main term. -/
def shannonError (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (lambda : ℝ) : ℝ := by
  letI := shannonIndexNonempty theta n
  exact entropyLine (shannonLineData theta n z) 1 lambda -
    shannonMain theta n z lambda

/-- Uniform compact `C²` error of the Shannon expansion. -/
def shannonCtwoError (theta : ShannonData) (K : Set (ℝ × ℝ))
    (lambda0 : ℝ) (j n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ z ∈ K, ∃ lambda ∈ Icc (-lambda0) lambda0,
    r = |iteratedDeriv (shannonError theta n z) j lambda|}

end ConditionalEntropy
