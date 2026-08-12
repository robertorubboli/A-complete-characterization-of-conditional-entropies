import ConditionalEntropy.Basic
import Mathlib.Analysis.MeanInequalities

/-!
# Standalone curvature proofs

This file verifies the coefficient calculations behind Lemma 4.2,
Propositions 5.1--5.3, Proposition 5.6, and the tropical obstruction.
-/

open scoped BigOperators

namespace ConditionalEntropy

theorem monomialCurvature_eq_neg_variance {ι : Type*} [Fintype ι]
    (β a : ι → ℝ) (hsum : IsAffineFamily β) :
    monomialCurvature β a = -∑ i, β i * (a i - ∑ j, β j * a j) ^ 2 := by
  let S : ℝ := ∑ j, β j * a j
  have hcenter :
      (∑ i, β i * (a i - S) ^ 2) =
        (∑ i, β i * a i ^ 2) - 2 * S * (∑ i, β i * a i) + S ^ 2 * (∑ i, β i) := by
    calc
      (∑ i, β i * (a i - S) ^ 2) =
          ∑ i, (β i * a i ^ 2 - 2 * S * (β i * a i) + S ^ 2 * β i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = (∑ i, β i * a i ^ 2) - 2 * S * (∑ i, β i * a i) +
          S ^ 2 * (∑ i, β i) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            simp only [Finset.mul_sum]
  simp only [IsAffineFamily] at hsum
  rw [monomialCurvature, show (∑ j, β j * a j) = S from rfl, hcenter, hsum]
  ring

theorem monomialCurvature_nonpos_of_nonneg {ι : Type*} [Fintype ι]
    (β a : ι → ℝ) (hβ : ∀ i, 0 ≤ β i) (hsum : IsAffineFamily β) :
    monomialCurvature β a ≤ 0 := by
  rw [monomialCurvature_eq_neg_variance β a hsum]
  simp only [neg_nonpos]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hβ i) (sq_nonneg _)

theorem coefficient_mem_Icc_of_curvature_nonpos {ι : Type*} [Fintype ι]
    (β : ι → ℝ) (hcurv : ∀ a, monomialCurvature β a ≤ 0) (k : ι) :
    β k ∈ Set.Icc 0 1 := by
  classical
  let a : ι → ℝ := fun i => if i = k then 1 else 0
  have h := hcurv a
  have hsum : (∑ i, β i * a i) = β k := by
    simp [a]
  have hsq : (∑ i, β i * (a i) ^ 2) = β k := by
    simp [a]
  rw [monomialCurvature, hsum, hsq] at h
  constructor <;> nlinarith

theorem monomialCurvature_pos_of_negative_coefficient {ι : Type*} [Fintype ι]
    (β : ι → ℝ) {k : ι} (hk : β k < 0) :
    ∃ a, 0 < monomialCurvature β a := by
  classical
  let a : ι → ℝ := fun i => if i = k then 1 else 0
  refine ⟨a, ?_⟩
  simp [monomialCurvature, a]
  nlinarith

theorem two_positive_stationary_witness {A C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    C * (1 / C) + A * (-1 / A) = 0 ∧
      -(C * (1 / C) ^ 2 + A * (-1 / A) ^ 2) < 0 := by
  constructor
  · field_simp
    norm_num
  · have hA0 : A ≠ 0 := ne_of_gt hA
    have hC0 : C ≠ 0 := ne_of_gt hC
    rw [show -(C * (1 / C) ^ 2 + A * (-1 / A) ^ 2) = -(1 / C + 1 / A) by
      field_simp]
    have : 0 < 1 / C + 1 / A := add_pos (one_div_pos.mpr hC) (one_div_pos.mpr hA)
    linarith

theorem negative_tail_concavity_obstruction {A : ℝ} (hA : A < 0) :
    0 < A ^ 2 - A := by nlinarith [sq_nonneg A]

theorem excessive_lower_moment_concavity_obstruction {B : ℝ} (hB : 1 < B) :
    0 < B ^ 2 - B := by nlinarith

theorem shannon_atom_concavity_obstruction {m : ℝ} (hm : m ≠ 0) :
    0 < m ^ 2 := sq_pos_of_ne_zero hm

theorem positive_tail_derivation_obstruction {A : ℝ} (hA : A < 0) :
    0 < -A := neg_pos.mpr hA

end ConditionalEntropy
