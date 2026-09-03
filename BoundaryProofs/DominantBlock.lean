import ConditionalEntropy.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dominant-block estimates

This file supplies the dominant-block estimates packaged by Lemma A.12 of the
complete-proof document.  A finite probability weight concentrated on one
block has its first and second logarithmic power-mean derivatives close to the
values on that block.  The proof uses only finite sums, the triangle
inequality, and nonnegativity of squares.
-/

open scoped BigOperators

namespace ConditionalEntropy

noncomputable def weightedMean {ι : Type*} [Fintype ι]
    (π u : ι → ℝ) : ℝ :=
  ∑ i, π i * u i

noncomputable def weightedSecondMoment {ι : Type*} [Fintype ι]
    (π u : ι → ℝ) : ℝ :=
  ∑ i, π i * u i ^ 2

noncomputable def weightedVariance {ι : Type*} [Fintype ι]
    (π u : ι → ℝ) : ℝ :=
  weightedSecondMoment π u - weightedMean π u ^ 2

private theorem weighted_sum_sub_center
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π u : ι → ℝ) (j : ι) (hsum : ∑ i, π i = 1) :
    weightedMean π u - u j = ∑ i ∈ Finset.univ.erase j, π i * (u i - u j) := by
  rw [weightedMean]
  have hπ := Finset.sum_erase_add Finset.univ (f := π) (Finset.mem_univ j)
  have hπu := Finset.sum_erase_add Finset.univ
    (f := fun i => π i * u i) (Finset.mem_univ j)
  calc
    (∑ i, π i * u i) - u j =
        ((∑ i ∈ Finset.univ.erase j, π i * u i) + π j * u j) -
          ((∑ i ∈ Finset.univ.erase j, π i) + π j) * u j := by
            rw [hπu, hπ, hsum]
            ring
    _ = ∑ i ∈ Finset.univ.erase j, π i * (u i - u j) := by
      rw [show (∑ i ∈ Finset.univ.erase j, π i * (u i - u j)) =
          (∑ i ∈ Finset.univ.erase j, π i * u i) -
            (∑ i ∈ Finset.univ.erase j, π i) * u j by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.sum_mul]]
      ring

private theorem off_block_mass_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π : ι → ℝ) (j : ι) {δ : ℝ}
    (hsum : ∑ i, π i = 1) (hdominant : 1 - δ ≤ π j) :
    ∑ i ∈ Finset.univ.erase j, π i ≤ δ := by
  have hsplit := Finset.sum_erase_add Finset.univ (f := π) (Finset.mem_univ j)
  rw [hsum] at hsplit
  linarith

private theorem weighted_deviation_le
    {ι : Type*} [Fintype ι]
    (π u : ι → ℝ) (j : ι) {δ B : ℝ}
    (hπ : ∀ i, 0 ≤ π i) (hsum : ∑ i, π i = 1)
    (hdominant : 1 - δ ≤ π j)
    (hdist : ∀ i, |u i - u j| ≤ B) (hB : 0 ≤ B) :
    |weightedMean π u - u j| ≤ B * δ := by
  classical
  rw [weighted_sum_sub_center π u j hsum]
  calc
    |∑ i ∈ Finset.univ.erase j, π i * (u i - u j)|
        ≤ ∑ i ∈ Finset.univ.erase j, |π i * (u i - u j)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.univ.erase j, π i * |u i - u j| := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul, abs_of_nonneg (hπ i)]
    _ ≤ ∑ i ∈ Finset.univ.erase j, π i * B := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hdist i) (hπ i)
    _ = B * ∑ i ∈ Finset.univ.erase j, π i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ ≤ B * δ := mul_le_mul_of_nonneg_left
          (off_block_mass_le π j hsum hdominant) hB

private theorem weightedVariance_eq_centered
    {ι : Type*} [Fintype ι]
    (π u : ι → ℝ) (hsum : ∑ i, π i = 1) :
    weightedVariance π u = ∑ i, π i * (u i - weightedMean π u) ^ 2 := by
  rw [weightedVariance, weightedSecondMoment]
  let m := weightedMean π u
  have hmean : ∑ i, π i * u i = m := rfl
  have hexpand :
      (∑ i, π i * (u i - m) ^ 2) =
        (∑ i, π i * u i ^ 2) - 2 * m * (∑ i, π i * u i) +
          m ^ 2 * (∑ i, π i) := by
    calc
      (∑ i, π i * (u i - m) ^ 2) =
          ∑ i, (π i * u i ^ 2 - 2 * m * (π i * u i) + m ^ 2 * π i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = (∑ i, π i * u i ^ 2) - 2 * m * (∑ i, π i * u i) +
          m ^ 2 * (∑ i, π i) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            simp only [Finset.mul_sum]
  rw [hexpand, hmean, hsum]
  ring

private theorem weightedVariance_nonneg
    {ι : Type*} [Fintype ι]
    (π u : ι → ℝ) (hπ : ∀ i, 0 ≤ π i) (hsum : ∑ i, π i = 1) :
    0 ≤ weightedVariance π u := by
  rw [weightedVariance_eq_centered π u hsum]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hπ i) (sq_nonneg _)

private theorem weightedVariance_le_center
    {ι : Type*} [Fintype ι]
    (π u : ι → ℝ) (c : ℝ) (hsum : ∑ i, π i = 1) :
    weightedVariance π u ≤ ∑ i, π i * (u i - c) ^ 2 := by
  let m := weightedMean π u
  have hmean : ∑ i, π i * u i = m := rfl
  rw [weightedVariance]
  have hcenter :
      (∑ i, π i * (u i - c) ^ 2) =
        weightedSecondMoment π u - 2 * c * m + c ^ 2 := by
    calc
      (∑ i, π i * (u i - c) ^ 2) =
          ∑ i, (π i * u i ^ 2 - 2 * c * (π i * u i) + c ^ 2 * π i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = (∑ i, π i * u i ^ 2) - 2 * c * (∑ i, π i * u i) +
            c ^ 2 * (∑ i, π i) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            simp only [Finset.mul_sum]
      _ = weightedSecondMoment π u - 2 * c * m + c ^ 2 := by
        rw [weightedSecondMoment, hmean, hsum]
        ring
  rw [hcenter]
  nlinarith [sq_nonneg (m - c)]

/-- First dominant-block estimate used in Lemma A.12. -/
theorem dominantBlock_first
    {ι : Type*} [Fintype ι]
    (π u : ι → ℝ) (j : ι) {δ M : ℝ}
    (hπ : ∀ i, 0 ≤ π i) (hsum : ∑ i, π i = 1)
    (hdominant : 1 - δ ≤ π j) (hM : ∀ i, |u i| ≤ M) (hM0 : 0 ≤ M) :
    |weightedMean π u - u j| ≤ 2 * M * δ := by
  apply weighted_deviation_le π u j hπ hsum hdominant
  · intro i
    calc
      |u i - u j| ≤ |u i| + |u j| := abs_sub _ _
      _ ≤ 2 * M := by linarith [hM i, hM j]
  · linarith

/-- Second dominant-block estimate used in Lemma A.12. -/
theorem dominantBlock_second
    {ι : Type*} [Fintype ι]
    (π u : ι → ℝ) (j : ι) {α δ M : ℝ}
    (hπ : ∀ i, 0 ≤ π i) (hsum : ∑ i, π i = 1)
    (hdominant : 1 - δ ≤ π j) (hM : ∀ i, |u i| ≤ M)
    (hα : 0 ≤ α) (_hM0 : 0 ≤ M) :
    |(-weightedSecondMoment π u + α * weightedVariance π u) + u j ^ 2|
      ≤ 2 * M ^ 2 * (1 + 2 * α) * δ := by
  have hsqdist : ∀ i, |u i ^ 2 - u j ^ 2| ≤ 2 * M ^ 2 := by
    intro i
    calc
      |u i ^ 2 - u j ^ 2| ≤ |u i ^ 2| + |u j ^ 2| := abs_sub _ _
      _ = |u i| ^ 2 + |u j| ^ 2 := by rw [abs_pow, abs_pow]
      _ ≤ 2 * M ^ 2 := by
        have hi := hM i
        have hj := hM j
        have hi2 := mul_self_le_mul_self (abs_nonneg (u i)) hi
        have hj2 := mul_self_le_mul_self (abs_nonneg (u j)) hj
        nlinarith
  have hsecond : |weightedSecondMoment π u - u j ^ 2| ≤ 2 * M ^ 2 * δ := by
    simpa [weightedSecondMoment, weightedMean] using
      (weighted_deviation_le π (fun i => u i ^ 2) j hπ hsum hdominant
        hsqdist (by positivity : 0 ≤ 2 * M ^ 2))
  have hvar0 := weightedVariance_nonneg π u hπ hsum
  have hvar : weightedVariance π u ≤ 4 * M ^ 2 * δ := by
    calc
      weightedVariance π u ≤ ∑ i, π i * (u i - u j) ^ 2 :=
        weightedVariance_le_center π u (u j) hsum
      _ = weightedMean π (fun i => (u i - u j) ^ 2) := by
        rw [weightedMean]
      _ ≤ 4 * M ^ 2 * δ := by
        have hdist : ∀ i,
            |(u i - u j) ^ 2 - (u j - u j) ^ 2| ≤ 4 * M ^ 2 := by
          intro i
          simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
            sub_zero, abs_sq]
          have : |u i - u j| ≤ 2 * M := by
            calc
              |u i - u j| ≤ |u i| + |u j| := abs_sub _ _
              _ ≤ 2 * M := by linarith [hM i, hM j]
          have hsquare := mul_self_le_mul_self (abs_nonneg (u i - u j)) this
          simp only [abs_mul_abs_self] at hsquare
          nlinarith
        have hdev := weighted_deviation_le π (fun i => (u i - u j) ^ 2) j hπ hsum
          hdominant hdist (by positivity : 0 ≤ 4 * M ^ 2)
        exact (le_abs_self _).trans (by simpa using hdev)
  calc
    |(-weightedSecondMoment π u + α * weightedVariance π u) + u j ^ 2|
        = |-(weightedSecondMoment π u - u j ^ 2) + α * weightedVariance π u| := by ring_nf
    _ ≤ |weightedSecondMoment π u - u j ^ 2| + |α * weightedVariance π u| := by
      simpa only [abs_neg] using abs_add_le (-(weightedSecondMoment π u - u j ^ 2))
        (α * weightedVariance π u)
    _ ≤ 2 * M ^ 2 * δ + α * (4 * M ^ 2 * δ) := by
      rw [abs_mul, abs_of_nonneg hα, abs_of_nonneg hvar0]
      gcongr
    _ = 2 * M ^ 2 * (1 + 2 * α) * δ := by ring

end ConditionalEntropy
