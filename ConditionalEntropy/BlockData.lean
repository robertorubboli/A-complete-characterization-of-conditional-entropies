import ConditionalEntropy.LineCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Finite block families

This file gives the proof-carrying dependent carriers used in the block
localisation arguments.  A block is represented literally by a sigma type;
there is no quotient, padding convention, or hidden nonemptiness assumption.
-/

noncomputable section

open Filter Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

/-- A finite disjoint union of blocks with prescribed cardinalities. -/
abbrev BlockIndex {J : ℕ} (n : Fin (J + 1) → ℕ) :=
  Σ j, Fin (n j)

/-- The vector which is constant with value `b j` on block `j`. -/
def blockVec {J : ℕ} (n : Fin (J + 1) → ℕ)
    (b : Fin (J + 1) → ℝ) : BlockIndex n → ℝ :=
  fun i ↦ b i.1

/-- Exponents and amplitudes defining an asymptotic block family. -/
structure BlockData (J : ℕ) where
  m : Fin (J + 1) → ℝ
  m_pos : ∀ j, 0 < m j
  a : Fin (J + 1) → ℝ

/-- The natural asymptotic scale, shifted so that it is always at least two. -/
def blockScale (n : ℕ) : ℝ :=
  n + 2

theorem blockScale_pos (n : ℕ) : 0 < blockScale n := by
  unfold blockScale
  exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num)

theorem one_le_blockScale (n : ℕ) : 1 ≤ blockScale n := by
  unfold blockScale
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The integral block multiplicity obtained by rounding `scale ^ m`. -/
def blockCount {J : ℕ} (B : BlockData J) (n : ℕ) (j : Fin (J + 1)) : ℕ :=
  Nat.ceil (Real.rpow (blockScale n) (B.m j))

/-- All block counts at a fixed scale. -/
abbrev blockCounts {J : ℕ} (B : BlockData J) (n : ℕ) : Fin (J + 1) → ℕ :=
  fun j ↦ blockCount B n j

/-- The dependent carrier of a rounded asymptotic block family. -/
abbrev BlockCarrier {J : ℕ} (B : BlockData J) (n : ℕ) :=
  BlockIndex (blockCounts B n)

/-- Every rounded block has at least one coordinate. -/
theorem blockCount_pos {J : ℕ} (B : BlockData J) (n : ℕ) (j : Fin (J + 1)) :
    0 < blockCount B n j := by
  rw [blockCount, Nat.ceil_pos]
  exact Real.rpow_pos_of_pos (blockScale_pos n) (B.m j)

/-- An explicit inhabitant of the carrier, used locally by extrema and entropy. -/
theorem blockCarrierNonempty {J : ℕ} (B : BlockData J) (n : ℕ) :
    Nonempty (BlockCarrier B n) :=
  ⟨⟨0, ⟨0, blockCount_pos B n 0⟩⟩⟩

/-- An explicit inhabitant of an arbitrary block carrier with positive counts. -/
theorem blockIndexNonempty {J : ℕ} (n : Fin (J + 1) → ℕ)
    (h_n : ∀ j, 1 ≤ n j) : Nonempty (BlockIndex n) :=
  ⟨⟨0, ⟨0, Nat.succ_le_iff.mp (h_n 0)⟩⟩⟩

/-- The maximum of a nonempty constant-on-block vector. -/
def blockMax {J : ℕ} (n : Fin (J + 1) → ℕ)
    (h_n : ∀ j, 1 ≤ n j) (b : Fin (J + 1) → ℝ) : ℝ := by
  letI := blockIndexNonempty n h_n
  exact finMax (blockVec n b)

/-- Positive base vector of an asymptotic block line. -/
def blockBase {J : ℕ} (B : BlockData J) (n : ℕ) : BlockCarrier B n → ℝ :=
  fun i ↦ Real.rpow (blockScale n) (B.a i.1)

/-- A velocity on blocks, repeated over every coordinate in each block. -/
def blockVelocity {J : ℕ} {B : BlockData J} {n : ℕ}
    (u : Fin (J + 1) → ℝ) : BlockCarrier B n → ℝ :=
  fun i ↦ u i.1

/-- The strictly positive multiplicative line associated to block data. -/
def blockLineData {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) : PositiveLineData (BlockCarrier B n) where
  x := blockBase B n
  u := blockVelocity u
  x_pos i := Real.rpow_pos_of_pos (blockScale_pos n) (B.a i.1)

/-- Raw coordinates of the block line. -/
def blockLineRaw {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) (lambda : ℝ) : BlockCarrier B n → ℝ :=
  lineRaw (blockLineData B n u) lambda

@[simp] theorem blockLineRaw_apply {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) (lambda : ℝ) (i : BlockCarrier B n) :
    blockLineRaw B n u lambda i =
      Real.rpow (blockScale n) (B.a i.1) * (1 + u i.1 * lambda) := by
  rfl

/-- Affine exponent governing the contribution of one block. -/
def blockExponent {J : ℕ} (B : BlockData J) (j : Fin (J + 1))
    (alpha : ℝ) : ℝ :=
  B.m j + B.a j * alpha

/-- Exact (rounded) contribution of one block to a power sum. -/
def blockContribution {J : ℕ} (B : BlockData J) (n : ℕ)
    (j : Fin (J + 1)) (alpha : ℝ) : ℝ :=
  (blockCount B n j : ℝ) *
    Real.rpow (Real.rpow (blockScale n) (B.a j)) alpha

/-- Exact escort mass carried by one block. -/
def blockEscort {J : ℕ} (B : BlockData J) (n : ℕ)
    (j : Fin (J + 1)) (alpha : ℝ) : ℝ :=
  blockContribution B n j alpha /
    ∑ l, blockContribution B n l alpha

/-- Blockwise escort mean. -/
def blockEscortMean {J : ℕ} (B : BlockData J) (n : ℕ) (alpha : ℝ)
    (u : Fin (J + 1) → ℝ) : ℝ :=
  ∑ j, blockEscort B n j alpha * u j

/-- Blockwise escort second moment. -/
def blockEscortSecond {J : ℕ} (B : BlockData J) (n : ℕ) (alpha : ℝ)
    (u : Fin (J + 1) → ℝ) : ℝ :=
  ∑ j, blockEscort B n j alpha * (u j) ^ 2

/-- Blockwise escort variance. -/
def blockEscortVar {J : ℕ} (B : BlockData J) (n : ℕ) (alpha : ℝ)
    (u : Fin (J + 1) → ℝ) : ℝ :=
  blockEscortSecond B n alpha u - (blockEscortMean B n alpha u) ^ 2

/-- First entropy-line derivative kernel at the block base point. -/
def blockKernelFirst {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) (beta : Param) : ℝ := by
  letI := blockCarrierNonempty B n
  exact entropyLineFirst (blockLineData B n u) beta 0

/-- Second entropy-line derivative kernel at the block base point. -/
def blockKernelSecond {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) (beta : Param) : ℝ := by
  letI := blockCarrierNonempty B n
  exact entropyLineSecond (blockLineData B n u) beta 0

section BlockVectorFormulas

/-- Pointwise nonnegativity is inherited from the block values. -/
theorem blockVec_nonneg {J : ℕ} (n : Fin (J + 1) → ℕ)
    (b : Fin (J + 1) → ℝ) (h_b : ∀ j, 0 ≤ b j) :
    ∀ i : BlockIndex n, 0 ≤ blockVec n b i :=
  fun i ↦ h_b i.1

/-- Summing a block-constant vector multiplies each value by its block size. -/
theorem l1Mass_blockVec {J : ℕ} (n : Fin (J + 1) → ℕ)
    (b : Fin (J + 1) → ℝ) :
    l1Mass (blockVec n b) = ∑ j, (n j : ℝ) * b j := by
  change (∑ i : Σ j, Fin (n j), b i.1) = _
  rw [Fintype.sum_sigma]
  simp

/-- The same block decomposition holds for every real power. -/
theorem sum_rpow_blockVec {J : ℕ} (n : Fin (J + 1) → ℕ)
    (b : Fin (J + 1) → ℝ) (alpha : ℝ) :
    ∑ i, Real.rpow (blockVec n b i) alpha =
      ∑ j, (n j : ℝ) * Real.rpow (b j) alpha := by
  change (∑ i : Σ j, Fin (n j), Real.rpow (b i.1) alpha) = _
  rw [Fintype.sum_sigma]
  simp

/-- A point is bounded by the maximum of any finite nonempty real family. -/
theorem le_finMax_family {I : Type*} [Fintype I] [Nonempty I]
    (a : I → ℝ) (i : I) : a i ≤ finMax a := by
  unfold finMax
  exact Finset.le_sup' a (Finset.mem_univ i)

/-- Repeating values over nonempty blocks does not change their maximum. -/
theorem blockMax_eq_finMax {J : ℕ} (n : Fin (J + 1) → ℕ)
    (h_n : ∀ j, 1 ≤ n j) (b : Fin (J + 1) → ℝ) :
    blockMax n h_n b = finMax b := by
  letI := blockIndexNonempty n h_n
  change finMax (blockVec n b) = finMax b
  apply le_antisymm
  · obtain ⟨i, hi⟩ := finMax_mem (blockVec n b)
    calc
      finMax (blockVec n b) = blockVec n b i := hi.symm
      _ = b i.1 := rfl
      _ ≤ finMax b := le_finMax_family b i.1
  · obtain ⟨j, hj⟩ := finMax_mem b
    let i : BlockIndex n := ⟨j, ⟨0, Nat.succ_le_iff.mp (h_n j)⟩⟩
    calc
      finMax b = b j := hj.symm
      _ = blockVec n b i := rfl
      _ ≤ finMax (blockVec n b) := le_finMax_family (blockVec n b) i

/-- A nonnegative block vector is nonzero exactly when one block is positive. -/
theorem blockVec_ne_zero_iff {J : ℕ} (n : Fin (J + 1) → ℕ)
    (h_n : ∀ j, 1 ≤ n j) (b : Fin (J + 1) → ℝ)
    (h_b : ∀ j, 0 ≤ b j) :
    blockVec n b ≠ 0 ↔ ∃ j : Fin (J + 1), 0 < b j := by
  constructor
  · intro hv
    by_contra h
    push Not at h
    have hb0 : b = 0 := by
      funext j
      exact le_antisymm (h j) (h_b j)
    apply hv
    rw [hb0]
    funext i
    rfl
  · rintro ⟨j, hj⟩ hv
    let i : BlockIndex n := ⟨j, ⟨0, Nat.succ_le_iff.mp (h_n j)⟩⟩
    have hi := congrFun hv i
    change b j = 0 at hi
    linarith

/-- The literal conjunction of finite-sum, power-sum, maximum, and support
formulas used by the manuscript's block construction. -/
theorem blockVectorFormulas {J : ℕ} (n : Fin (J + 1) → ℕ)
    (h_n : ∀ j, 1 ≤ n j) (b : Fin (J + 1) → ℝ)
    (h_b : ∀ j, 0 ≤ b j) :
    (∀ i : BlockIndex n, 0 ≤ blockVec n b i) ∧
      l1Mass (blockVec n b) = ∑ j, (n j : ℝ) * b j ∧
      (∀ alpha : ℝ, 0 < alpha →
        ∑ i, Real.rpow (blockVec n b i) alpha =
          ∑ j, (n j : ℝ) * Real.rpow (b j) alpha) ∧
      blockMax n h_n b = finMax b ∧
      (blockVec n b ≠ 0 ↔ ∃ j : Fin (J + 1), 0 < b j) := by
  exact ⟨blockVec_nonneg n b h_b, l1Mass_blockVec n b,
    fun alpha _ ↦ sum_rpow_blockVec n b alpha,
    blockMax_eq_finMax n h_n b, blockVec_ne_zero_iff n h_n b h_b⟩

end BlockVectorFormulas

section BlockEscortIdentities

/-- The raw power sum of the block base is exactly the sum of the declared
rounded block contributions. -/
theorem sum_rpow_blockBase_eq_contributions {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) :
    ∑ i : BlockCarrier B n, (blockBase B n i) ^ alpha =
      ∑ j, blockContribution B n j alpha := by
  simpa [BlockCarrier, blockBase, blockCounts, blockContribution, blockVec] using
    (sum_rpow_blockVec (blockCounts B n)
      (fun j ↦ Real.rpow (blockScale n) (B.a j)) alpha)

/-- Every rounded block contribution is strictly positive. -/
theorem blockContribution_pos {J : ℕ} (B : BlockData J) (n : ℕ)
    (j : Fin (J + 1)) (alpha : ℝ) :
    0 < blockContribution B n j alpha := by
  apply mul_pos
  · exact_mod_cast blockCount_pos B n j
  · exact Real.rpow_pos_of_pos
      (Real.rpow_pos_of_pos (blockScale_pos n) (B.a j)) alpha

/-- The normalizing denominator for block escorts is positive. -/
theorem sum_blockContribution_pos {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) :
    0 < ∑ j, blockContribution B n j alpha := by
  exact Finset.sum_pos (fun j _ ↦ blockContribution_pos B n j alpha)
    Finset.univ_nonempty

theorem blockEscort_nonneg {J : ℕ} (B : BlockData J) (n : ℕ)
    (j : Fin (J + 1)) (alpha : ℝ) :
    0 ≤ blockEscort B n j alpha := by
  exact (div_pos (blockContribution_pos B n j alpha)
    (sum_blockContribution_pos B n alpha)).le

/-- Block escort masses form a probability vector. -/
theorem sum_blockEscort {J : ℕ} (B : BlockData J) (n : ℕ)
    (alpha : ℝ) :
    ∑ j, blockEscort B n j alpha = 1 := by
  unfold blockEscort
  rw [← Finset.sum_div]
  exact div_self (sum_blockContribution_pos B n alpha).ne'

/-- At the base point, summing coordinate escort weights over one block
recovers its declared block escort mass. -/
theorem sum_escortWeight_blockLine_zero {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (alpha : ℝ)
    (j : Fin (J + 1)) :
    ∑ i : Fin (blockCount B n j),
      escortWeight (blockLineData B n u) alpha 0 ⟨j, i⟩ =
        blockEscort B n j alpha := by
  simp only [escortWeight, lineRaw, blockLineData, mul_zero, add_zero, mul_one]
  rw [sum_rpow_blockBase_eq_contributions]
  change (∑ _i : Fin (blockCount B n j),
      Real.rpow (Real.rpow (blockScale n) (B.a j)) alpha /
        (∑ l, blockContribution B n l alpha)) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold blockEscort blockContribution
  ring

/-- Any statistic constant on blocks can be summed using block escorts. -/
theorem sum_escortWeight_mul_blockValue {J : ℕ} (B : BlockData J)
    (n : ℕ) (u v : Fin (J + 1) → ℝ) (alpha : ℝ) :
    ∑ i : BlockCarrier B n,
      escortWeight (blockLineData B n u) alpha 0 i * v i.1 =
        ∑ j, blockEscort B n j alpha * v j := by
  change (∑ i : Σ j, Fin (blockCount B n j),
    escortWeight (blockLineData B n u) alpha 0 i * v i.1) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ i ∈ Finset.univ,
    escortWeight (blockLineData B n u) alpha 0 ⟨j, i⟩ * v j) = _
  rw [← Finset.sum_mul, sum_escortWeight_blockLine_zero]

/-- The line-data escort mean is literally the block escort mean. -/
theorem escortMean_blockLine_zero {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) (alpha : ℝ) :
    escortMean (blockLineData B n u) alpha 0 =
      blockEscortMean B n alpha u := by
  simpa [escortMean, effectiveVelocity, blockVelocity, blockEscortMean,
    blockLineData] using sum_escortWeight_mul_blockValue B n u u alpha

/-- The line-data escort second moment is literally the block second moment. -/
theorem escortSecond_blockLine_zero {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) (alpha : ℝ) :
    escortSecond (blockLineData B n u) alpha 0 =
      blockEscortSecond B n alpha u := by
  simpa [escortSecond, effectiveVelocity, blockVelocity, blockEscortSecond,
    blockLineData] using
      sum_escortWeight_mul_blockValue B n u (fun j ↦ (u j) ^ 2) alpha

/-- The line-data escort variance is literally the block variance. -/
theorem escortVar_blockLine_zero {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) (alpha : ℝ) :
    escortVar (blockLineData B n u) alpha 0 =
      blockEscortVar B n alpha u := by
  rw [escortVar, blockEscortVar, escortMean_blockLine_zero,
    escortSecond_blockLine_zero]

/-- Exact finite-order formula for the first block kernel away from order one. -/
theorem blockKernelFirst_finite {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) {alpha : ℝ} (h_alpha : 0 < alpha)
    (h_one : alpha ≠ 1) :
    blockKernelFirst B n u (finiteParam alpha) =
      singularWeight (finiteParam alpha) *
        (blockEscortMean B n alpha u - blockEscortMean B n 1 u) := by
  letI := blockCarrierNonempty B n
  rw [blockKernelFirst, entropyLineFirst_finite_zero _ h_alpha h_one,
    escortMean_blockLine_zero, escortMean_blockLine_zero]

/-- Exact finite-order formula for the second block kernel away from order one. -/
theorem blockKernelSecond_finite {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) {alpha : ℝ} (h_alpha : 0 < alpha)
    (h_one : alpha ≠ 1) :
    blockKernelSecond B n u (finiteParam alpha) =
      -alpha * blockEscortVar B n alpha u +
        singularWeight (finiteParam alpha) *
          ((blockEscortMean B n 1 u) ^ 2 -
            (blockEscortMean B n alpha u) ^ 2) := by
  letI := blockCarrierNonempty B n
  rw [blockKernelSecond, entropyLineSecond_finite_zero _ h_alpha h_one,
    escortVar_blockLine_zero, escortMean_blockLine_zero,
    escortMean_blockLine_zero]

end BlockEscortIdentities

section Rounding

/-- The ceiling error for a positive power is at most one inverse power. -/
theorem ceil_rpow_ratio_bounds (s : ℝ) (d : ℕ) (_h_s : 0 < s) (h_d : 1 ≤ d) :
    1 ≤ (Nat.ceil (Real.rpow (d : ℝ) s) : ℝ) /
        Real.rpow (d : ℝ) s ∧
      (Nat.ceil (Real.rpow (d : ℝ) s) : ℝ) /
        Real.rpow (d : ℝ) s ≤
          1 + Real.rpow (d : ℝ) (-s) := by
  have hdposNat : 0 < d := lt_of_lt_of_le Nat.zero_lt_one h_d
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hdposNat
  have hx : 0 < Real.rpow (d : ℝ) s := Real.rpow_pos_of_pos hdpos s
  constructor
  · exact (one_le_div hx).2 (Nat.le_ceil _)
  · rw [div_le_iff₀ hx]
    calc
      (Nat.ceil (Real.rpow (d : ℝ) s) : ℝ)
          ≤ Real.rpow (d : ℝ) s + 1 :=
        (Nat.ceil_lt_add_one hx.le).le
      _ = (1 + Real.rpow (d : ℝ) (-s)) * Real.rpow (d : ℝ) s := by
        have hneg : Real.rpow (d : ℝ) (-s) =
            (Real.rpow (d : ℝ) s)⁻¹ := Real.rpow_neg hdpos.le s
        rw [hneg]
        field_simp [hx.ne']

/-- Logarithmic form of the ceiling error estimate. -/
theorem log_ceil_rpow_ratio_bounds (s : ℝ) (d : ℕ)
    (h_s : 0 < s) (h_d : 1 ≤ d) :
    0 ≤ Real.log ((Nat.ceil (Real.rpow (d : ℝ) s) : ℝ) /
        Real.rpow (d : ℝ) s) ∧
      Real.log ((Nat.ceil (Real.rpow (d : ℝ) s) : ℝ) /
          Real.rpow (d : ℝ) s) ≤
        Real.log (1 + Real.rpow (d : ℝ) (-s)) ∧
      Real.log (1 + Real.rpow (d : ℝ) (-s)) ≤
        Real.rpow (d : ℝ) (-s) := by
  have hR := ceil_rpow_ratio_bounds s d h_s h_d
  have hdposNat : 0 < d := lt_of_lt_of_le Nat.zero_lt_one h_d
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hdposNat
  have hx : 0 < Real.rpow (d : ℝ) s := Real.rpow_pos_of_pos hdpos s
  have hceilNat : 0 < Nat.ceil (Real.rpow (d : ℝ) s) :=
    Nat.ceil_pos.mpr hx
  have hceil : 0 < (Nat.ceil (Real.rpow (d : ℝ) s) : ℝ) := by
    exact_mod_cast hceilNat
  have hratio : 0 < (Nat.ceil (Real.rpow (d : ℝ) s) : ℝ) /
      Real.rpow (d : ℝ) s := div_pos hceil hx
  have hneg : 0 ≤ Real.rpow (d : ℝ) (-s) :=
    Real.rpow_nonneg hdpos.le (-s)
  have honeplus : 0 < 1 + Real.rpow (d : ℝ) (-s) := by linarith
  refine ⟨Real.log_nonneg hR.1, ?_, ?_⟩
  · exact Real.strictMonoOn_log.monotoneOn hratio honeplus hR.2
  · have h := Real.log_le_sub_one_of_pos honeplus
    linarith

/-- Negative powers decrease with the exponent and tend to zero uniformly
on every ray whose exponent is bounded below by a positive number. -/
theorem rpow_negative_monotone_and_tendsto (s₀ : ℝ) (h_s₀ : 0 < s₀) :
    (∀ (s : ℝ) (d : ℕ), s₀ ≤ s → 1 ≤ d →
      Real.rpow (d : ℝ) (-s) ≤ Real.rpow (d : ℝ) (-s₀)) ∧
      Tendsto (fun d : ℕ ↦ (d : ℝ) ^ (-s₀)) atTop (nhds 0) := by
  constructor
  · intro s d hs hd
    have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast hd
    exact Real.rpow_le_rpow_of_exponent_le hdreal (neg_le_neg hs)
  · have ht := (tendsto_rpow_neg_atTop h_s₀).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    change Tendsto (fun d : ℕ ↦ (d : ℝ) ^ (-s₀)) atTop (nhds 0) at ht
    exact ht

/-- The manuscript's complete rounding package, stated as one literal
conjunction for direct statement-by-statement correspondence. -/
theorem roundingEstimates :
    (∀ (s : ℝ) (d : ℕ), 0 < s → 1 ≤ d →
      1 ≤ (Nat.ceil (Real.rpow (d : ℝ) s) : ℝ) /
          Real.rpow (d : ℝ) s ∧
        (Nat.ceil (Real.rpow (d : ℝ) s) : ℝ) /
            Real.rpow (d : ℝ) s ≤
          1 + Real.rpow (d : ℝ) (-s)) ∧
    (∀ (s : ℝ) (d : ℕ), 0 < s → 1 ≤ d →
      0 ≤ Real.log ((Nat.ceil (Real.rpow (d : ℝ) s) : ℝ) /
          Real.rpow (d : ℝ) s) ∧
        Real.log ((Nat.ceil (Real.rpow (d : ℝ) s) : ℝ) /
            Real.rpow (d : ℝ) s) ≤
          Real.log (1 + Real.rpow (d : ℝ) (-s)) ∧
        Real.log (1 + Real.rpow (d : ℝ) (-s)) ≤
          Real.rpow (d : ℝ) (-s)) ∧
    (∀ (s₀ : ℝ), 0 < s₀ →
      (∀ (s : ℝ) (d : ℕ), s₀ ≤ s → 1 ≤ d →
        Real.rpow (d : ℝ) (-s) ≤ Real.rpow (d : ℝ) (-s₀)) ∧
      Tendsto (fun d : ℕ ↦ (d : ℝ) ^ (-s₀)) atTop (nhds 0)) := by
  exact ⟨fun s d hs hd ↦ ceil_rpow_ratio_bounds s d hs hd,
    fun s d hs hd ↦ log_ceil_rpow_ratio_bounds s d hs hd,
    fun s₀ hs₀ ↦ rpow_negative_monotone_and_tendsto s₀ hs₀⟩

end Rounding

section DominantBlock

/-- A rounded count lies above its unrounded real value. -/
theorem rpow_le_blockCount {J : ℕ} (B : BlockData J) (n : ℕ)
    (j : Fin (J + 1)) :
    Real.rpow (blockScale n) (B.m j) ≤ (blockCount B n j : ℝ) := by
  exact Nat.le_ceil _

/-- A rounded count is at most twice its unrounded value. -/
theorem blockCount_le_two_mul_rpow {J : ℕ} (B : BlockData J) (n : ℕ)
    (j : Fin (J + 1)) :
    (blockCount B n j : ℝ) ≤
      2 * Real.rpow (blockScale n) (B.m j) := by
  have hxpos : 0 < Real.rpow (blockScale n) (B.m j) :=
    Real.rpow_pos_of_pos (blockScale_pos n) (B.m j)
  have hxone : 1 ≤ Real.rpow (blockScale n) (B.m j) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le (one_le_blockScale n) (B.m_pos j).le
  calc
    (blockCount B n j : ℝ)
        ≤ Real.rpow (blockScale n) (B.m j) + 1 :=
      (Nat.ceil_lt_add_one hxpos.le).le
    _ ≤ 2 * Real.rpow (blockScale n) (B.m j) := by linarith

/-- The ideal exponent power is a lower bound for the rounded contribution. -/
theorem rpow_blockExponent_le_contribution {J : ℕ} (B : BlockData J)
    (n : ℕ) (j : Fin (J + 1)) (alpha : ℝ) :
    Real.rpow (blockScale n) (blockExponent B j alpha) ≤
      blockContribution B n j alpha := by
  have hd : 0 ≤ blockScale n := (blockScale_pos n).le
  have ha_nonneg : 0 ≤ Real.rpow (blockScale n) (B.a j * alpha) :=
    Real.rpow_nonneg hd _
  rw [blockExponent, blockContribution]
  simp only [Real.rpow_eq_pow] at *
  rw [← Real.rpow_mul hd (B.a j) alpha,
    Real.rpow_add (blockScale_pos n) (B.m j) (B.a j * alpha)]
  exact mul_le_mul_of_nonneg_right (rpow_le_blockCount B n j) ha_nonneg

/-- Rounding costs at most a factor two relative to the ideal exponent power. -/
theorem blockContribution_le_two_mul_rpowExponent {J : ℕ}
    (B : BlockData J) (n : ℕ) (j : Fin (J + 1)) (alpha : ℝ) :
    blockContribution B n j alpha ≤
      2 * Real.rpow (blockScale n) (blockExponent B j alpha) := by
  have hd : 0 ≤ blockScale n := (blockScale_pos n).le
  have ha_nonneg : 0 ≤ Real.rpow (blockScale n) (B.a j * alpha) :=
    Real.rpow_nonneg hd _
  rw [blockExponent, blockContribution]
  simp only [Real.rpow_eq_pow] at *
  rw [← Real.rpow_mul hd (B.a j) alpha,
    Real.rpow_add (blockScale_pos n) (B.m j) (B.a j * alpha)]
  calc
    (blockCount B n j : ℝ) * Real.rpow (blockScale n) (B.a j * alpha)
        ≤ (2 * Real.rpow (blockScale n) (B.m j)) *
            Real.rpow (blockScale n) (B.a j * alpha) :=
      mul_le_mul_of_nonneg_right (blockCount_le_two_mul_rpow B n j) ha_nonneg
    _ = 2 * (Real.rpow (blockScale n) (B.m j) *
          Real.rpow (blockScale n) (B.a j * alpha)) := by ring

/-- An exponent gap gives a pointwise contribution ratio with an explicit
rounding factor two. -/
theorem blockContribution_le_decay_mul {J : ℕ} (B : BlockData J)
    (n : ℕ) (k j : Fin (J + 1)) (alpha eta : ℝ)
    (hgap : eta ≤ blockExponent B k alpha - blockExponent B j alpha) :
    blockContribution B n j alpha ≤
      (2 * Real.rpow (blockScale n) (-eta)) *
        blockContribution B n k alpha := by
  have hd : 0 ≤ blockScale n := (blockScale_pos n).le
  have hexp : blockExponent B j alpha ≤ blockExponent B k alpha - eta := by
    linarith
  have hmono := Real.rpow_le_rpow_of_exponent_le (one_le_blockScale n) hexp
  have hneg_nonneg : 0 ≤ Real.rpow (blockScale n) (-eta) :=
    Real.rpow_nonneg hd _
  simp only [Real.rpow_eq_pow] at *
  calc
    blockContribution B n j alpha
        ≤ 2 * Real.rpow (blockScale n) (blockExponent B j alpha) :=
      blockContribution_le_two_mul_rpowExponent B n j alpha
    _ ≤ 2 * Real.rpow (blockScale n) (blockExponent B k alpha - eta) :=
      mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = (2 * Real.rpow (blockScale n) (-eta)) *
          Real.rpow (blockScale n) (blockExponent B k alpha) := by
      simp only [Real.rpow_eq_pow]
      rw [show blockExponent B k alpha - eta =
          blockExponent B k alpha + (-eta) by ring,
        Real.rpow_add (blockScale_pos n)]
      ring
    _ ≤ (2 * Real.rpow (blockScale n) (-eta)) *
          blockContribution B n k alpha :=
      mul_le_mul_of_nonneg_left
        (rpow_blockExponent_le_contribution B n k alpha)
        (mul_nonneg (by norm_num) hneg_nonneg)

/-- A dominant exponent suppresses every competing block escort. -/
theorem blockEscort_le_two_mul_decay {J : ℕ} (B : BlockData J)
    (n : ℕ) (k j : Fin (J + 1)) (alpha eta : ℝ)
    (hgap : eta ≤ blockExponent B k alpha - blockExponent B j alpha) :
    blockEscort B n j alpha ≤
      2 * Real.rpow (blockScale n) (-eta) := by
  have hkpos := blockContribution_pos B n k alpha
  have hjnonneg := (blockContribution_pos B n j alpha).le
  have hsum : blockContribution B n k alpha ≤
      ∑ l, blockContribution B n l alpha := by
    exact Finset.single_le_sum
      (fun l _ ↦ (blockContribution_pos B n l alpha).le)
      (Finset.mem_univ k)
  calc
    blockEscort B n j alpha = blockContribution B n j alpha /
        (∑ l, blockContribution B n l alpha) := rfl
    _ ≤ blockContribution B n j alpha / blockContribution B n k alpha :=
      div_le_div_of_nonneg_left hjnonneg hkpos hsum
    _ ≤ 2 * Real.rpow (blockScale n) (-eta) := by
      rw [div_le_iff₀ hkpos]
      exact blockContribution_le_decay_mul B n k j alpha eta hgap

/-- Quantitative outside-mass part of the dominant-block estimate.  The
constant is explicit and independent of the scale and order. -/
theorem dominantBlockOutsideMass {J : ℕ} (B : BlockData J)
    (I : Set ℝ) (k : Fin (J + 1)) (eta : ℝ)
    (hgap : ∀ alpha ∈ I, ∀ j : Fin (J + 1), j ≠ k →
      eta ≤ blockExponent B k alpha - blockExponent B j alpha) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (alpha : ℝ), alpha ∈ I →
        ∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha ≤
          C * Real.rpow (blockScale n) (-eta) := by
  let C : ℝ := 2 * Fintype.card (Fin (J + 1))
  refine ⟨C, by positivity, ?_⟩
  intro n alpha h_alpha
  have hdecay : 0 ≤ 2 * Real.rpow (blockScale n) (-eta) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (blockScale_pos n).le _)
  calc
    ∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha
        ≤ ∑ _j ∈ Finset.univ.erase k,
            2 * Real.rpow (blockScale n) (-eta) := by
      apply Finset.sum_le_sum
      intro j hj
      exact blockEscort_le_two_mul_decay B n k j alpha eta
        (hgap alpha h_alpha j (Finset.ne_of_mem_erase hj))
    _ = ((Finset.univ.erase k).card : ℝ) *
          (2 * Real.rpow (blockScale n) (-eta)) := by
      simp
    _ ≤ (Fintype.card (Fin (J + 1)) : ℝ) *
          (2 * Real.rpow (blockScale n) (-eta)) := by
      apply mul_le_mul_of_nonneg_right _ hdecay
      exact_mod_cast Finset.card_le_card (Finset.erase_subset k Finset.univ)
    _ = C * Real.rpow (blockScale n) (-eta) := by
      simp only [C]
      ring

/-- Centering a blockwise escort average at block `k` removes the `k` term
and leaves exactly the sum over the other blocks. -/
theorem blockEscortWeighted_sub_eq_sum_erase {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) (k : Fin (J + 1))
    (v : Fin (J + 1) → ℝ) :
    (∑ j, blockEscort B n j alpha * v j) - v k =
      ∑ j ∈ Finset.univ.erase k,
        blockEscort B n j alpha * (v j - v k) := by
  classical
  have hsum := sum_blockEscort B n alpha
  calc
    (∑ j, blockEscort B n j alpha * v j) - v k =
        (∑ j, blockEscort B n j alpha * v j) -
          v k * (∑ j, blockEscort B n j alpha) := by rw [hsum]; ring
    _ = ∑ j, blockEscort B n j alpha * (v j - v k) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    _ = ∑ j ∈ Finset.univ.erase k,
          blockEscort B n j alpha * (v j - v k) := by
      symm
      exact Finset.sum_erase Finset.univ (by simp)

/-- A general outside-mass bound for blockwise escort averages. -/
theorem abs_blockEscortWeighted_sub_le_outside {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) (k : Fin (J + 1))
    (v : Fin (J + 1) → ℝ) (D : ℝ)
    (hD : ∀ j, |v j - v k| ≤ D) :
    |(∑ j, blockEscort B n j alpha * v j) - v k| ≤
      D * (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha) := by
  rw [blockEscortWeighted_sub_eq_sum_erase]
  calc
    |∑ j ∈ Finset.univ.erase k,
        blockEscort B n j alpha * (v j - v k)|
        ≤ ∑ j ∈ Finset.univ.erase k,
            |blockEscort B n j alpha * (v j - v k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.univ.erase k,
          blockEscort B n j alpha * D := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (blockEscort_nonneg B n j alpha)]
      exact mul_le_mul_of_nonneg_left (hD j)
        (blockEscort_nonneg B n j alpha)
    _ = D * (∑ j ∈ Finset.univ.erase k,
          blockEscort B n j alpha) := by
      rw [← Finset.sum_mul]
      ring

/-- A bounded block velocity has mean error controlled by outside escort mass. -/
theorem abs_blockEscortMean_sub_le_outside {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) (k : Fin (J + 1))
    (u : Fin (J + 1) → ℝ) (U : ℝ)
    (h_u : ∀ j, |u j| ≤ U) :
    |blockEscortMean B n alpha u - u k| ≤
      (2 * U) *
        (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha) := by
  apply abs_blockEscortWeighted_sub_le_outside B n alpha k u (2 * U)
  intro j
  calc
    |u j - u k| ≤ |u j| + |u k| := abs_sub _ _
    _ ≤ U + U := add_le_add (h_u j) (h_u k)
    _ = 2 * U := by ring

/-- A bounded block velocity has second-moment error controlled by outside
escort mass. -/
theorem abs_blockEscortSecond_sub_le_outside {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) (k : Fin (J + 1))
    (u : Fin (J + 1) → ℝ) (U : ℝ) (h_U : 0 ≤ U)
    (h_u : ∀ j, |u j| ≤ U) :
    |blockEscortSecond B n alpha u - (u k) ^ 2| ≤
      (2 * U ^ 2) *
        (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha) := by
  apply abs_blockEscortWeighted_sub_le_outside B n alpha k
    (fun j ↦ (u j) ^ 2) (2 * U ^ 2)
  intro j
  have hj_sq : (u j) ^ 2 ≤ U ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_nonneg h_U] using h_u j)
  have hk_sq : (u k) ^ 2 ≤ U ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_nonneg h_U] using h_u k)
  calc
    |(u j) ^ 2 - (u k) ^ 2| ≤ |(u j) ^ 2| + |(u k) ^ 2| := abs_sub _ _
    _ = (u j) ^ 2 + (u k) ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    _ ≤ U ^ 2 + U ^ 2 := add_le_add hj_sq hk_sq
    _ = 2 * U ^ 2 := by ring

/-- Exact weighted square-deviation identity for block escorts. -/
theorem sum_blockEscort_mul_sub_sq {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) (u : Fin (J + 1) → ℝ) (c : ℝ) :
    ∑ j, blockEscort B n j alpha * (u j - c) ^ 2 =
      blockEscortSecond B n alpha u -
        2 * c * blockEscortMean B n alpha u + c ^ 2 := by
  have hsum := sum_blockEscort B n alpha
  simp_rw [show ∀ j : Fin (J + 1),
      blockEscort B n j alpha * (u j - c) ^ 2 =
        (blockEscort B n j alpha * (u j) ^ 2 -
          (2 * c) * (blockEscort B n j alpha * u j)) +
            c ^ 2 * blockEscort B n j alpha by
    intro j
    ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hsum]
  simp only [blockEscortSecond, blockEscortMean]
  ring

/-- Block escort variance is the weighted mean squared deviation. -/
theorem blockEscortVar_eq_sum_centered_sq {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) (u : Fin (J + 1) → ℝ) :
    blockEscortVar B n alpha u =
      ∑ j, blockEscort B n j alpha *
        (u j - blockEscortMean B n alpha u) ^ 2 := by
  rw [sum_blockEscort_mul_sub_sq]
  unfold blockEscortVar
  ring

theorem blockEscortVar_nonneg {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) (u : Fin (J + 1) → ℝ) :
    0 ≤ blockEscortVar B n alpha u := by
  rw [blockEscortVar_eq_sum_centered_sq]
  exact Finset.sum_nonneg fun j _ ↦
    mul_nonneg (blockEscort_nonneg B n j alpha) (sq_nonneg _)

/-- The escort variance of a bounded velocity is controlled by the outside
mass of any designated block. -/
theorem blockEscortVar_le_outside {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) (k : Fin (J + 1))
    (u : Fin (J + 1) → ℝ) (U : ℝ) (h_U : 0 ≤ U)
    (h_u : ∀ j, |u j| ≤ U) :
    blockEscortVar B n alpha u ≤
      (4 * U ^ 2) *
        (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha) := by
  have hsquare := sum_blockEscort_mul_sub_sq B n alpha u (u k)
  have hcenter : blockEscortVar B n alpha u ≤
      blockEscortSecond B n alpha u -
        2 * (u k) * blockEscortMean B n alpha u + (u k) ^ 2 := by
    unfold blockEscortVar
    nlinarith [sq_nonneg (blockEscortMean B n alpha u - u k)]
  calc
    blockEscortVar B n alpha u
        ≤ blockEscortSecond B n alpha u -
            2 * (u k) * blockEscortMean B n alpha u + (u k) ^ 2 := hcenter
    _ = ∑ j, blockEscort B n j alpha * (u j - u k) ^ 2 := hsquare.symm
    _ = ∑ j ∈ Finset.univ.erase k,
          blockEscort B n j alpha * (u j - u k) ^ 2 := by
      symm
      exact Finset.sum_erase Finset.univ (by simp)
    _ ≤ ∑ j ∈ Finset.univ.erase k,
          blockEscort B n j alpha * (4 * U ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      have hdiff : |u j - u k| ≤ 2 * U := by
        calc
          |u j - u k| ≤ |u j| + |u k| := abs_sub _ _
          _ ≤ U + U := add_le_add (h_u j) (h_u k)
          _ = 2 * U := by ring
      have hsquareDiff : (u j - u k) ^ 2 ≤ (2 * U) ^ 2 :=
        sq_le_sq.mpr (by
          rw [abs_of_nonneg (mul_nonneg (by norm_num) h_U)]
          exact hdiff)
      have hsquareDiff' : (u j - u k) ^ 2 ≤ 4 * U ^ 2 := by
        nlinarith
      exact mul_le_mul_of_nonneg_left hsquareDiff'
        (blockEscort_nonneg B n j alpha)
    _ = (4 * U ^ 2) *
          (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha) := by
      rw [← Finset.sum_mul]
      ring

/-- Dominant-block bounds for the first two escort moments, uniform in the
scale and in all bounded block velocities. -/
theorem dominantBlockMomentBounds {J : ℕ} (B : BlockData J)
    (I : Set ℝ) (k : Fin (J + 1)) (eta U : ℝ) (h_U : 0 ≤ U)
    (hgap : ∀ alpha ∈ I, ∀ j : Fin (J + 1), j ≠ k →
      eta ≤ blockExponent B k alpha - blockExponent B j alpha) :
    ∃ C_U : ℝ, 0 ≤ C_U ∧
      ∀ (u : Fin (J + 1) → ℝ), (∀ j, |u j| ≤ U) →
        ∀ (n : ℕ) (alpha : ℝ), alpha ∈ I →
          |blockEscortMean B n alpha u - u k| +
              |blockEscortSecond B n alpha u - (u k) ^ 2| +
              blockEscortVar B n alpha u ≤
            C_U * Real.rpow (blockScale n) (-eta) := by
  obtain ⟨C, hC, houtside⟩ := dominantBlockOutsideMass B I k eta hgap
  let A : ℝ := 2 * U + 2 * U ^ 2 + 4 * U ^ 2
  refine ⟨A * C, mul_nonneg ?_ hC, ?_⟩
  · dsimp [A]
    positivity
  · intro u hu n alpha h_alpha
    have hmean := abs_blockEscortMean_sub_le_outside B n alpha k u U hu
    have hsecond := abs_blockEscortSecond_sub_le_outside B n alpha k u U h_U hu
    have hvar := blockEscortVar_le_outside B n alpha k u U h_U hu
    have hA : 0 ≤ A := by
      dsimp [A]
      positivity
    calc
      |blockEscortMean B n alpha u - u k| +
          |blockEscortSecond B n alpha u - (u k) ^ 2| +
          blockEscortVar B n alpha u
          ≤ (2 * U) *
                (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha) +
              (2 * U ^ 2) *
                (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha) +
              (4 * U ^ 2) *
                (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha) :=
        add_le_add (add_le_add hmean hsecond) hvar
      _ = A * (∑ j ∈ Finset.univ.erase k,
            blockEscort B n j alpha) := by
        simp only [A]
        ring
      _ ≤ A * (C * Real.rpow (blockScale n) (-eta)) :=
        mul_le_mul_of_nonneg_left (houtside n alpha h_alpha) hA
      _ = (A * C) * Real.rpow (blockScale n) (-eta) := by ring

end DominantBlock

end ConditionalEntropy
