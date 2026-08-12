import ConditionalEntropy.ParameterConditions

/-!
# Sufficient coefficient conditions

These are the sign checks used after the power-mean/monomial factorisation in
Section 4.  They are independent of the later localization argument.
-/

open scoped BigOperators

namespace ConditionalEntropy

theorem positiveTemperate_coefficients_nonnegative
    {ι : Type*} [Fintype ι] (β : ι → ℝ)
    (hβ : ∀ i, 0 ≤ β i) (hsum : IsAffineFamily β) (a : ι → ℝ) :
    monomialCurvature β a ≤ 0 :=
  monomialCurvature_nonpos_of_nonneg β a hβ hsum

theorem negativeTemperate_two_coefficient_curvature
    {A B : ℝ} (hA : 0 < A) (hB : B ≤ 0) (hsum : A + B = 1) (u v : ℝ) :
    A * u + B * v = 0 → 0 ≤ -(A * u ^ 2 + B * v ^ 2) := by
  intro hstationary
  have hidentity :
      (A * u + B * v) ^ 2 - (A * u ^ 2 + B * v ^ 2) =
        -(A * B) * (u - v) ^ 2 := by
    have hB : B = 1 - A := by linarith
    rw [hB]
    ring
  calc
    0 ≤ -(A * B) * (u - v) ^ 2 :=
      mul_nonneg (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hA.le hB)) (sq_nonneg _)
    _ = (A * u + B * v) ^ 2 - (A * u ^ 2 + B * v ^ 2) := hidentity.symm
    _ = -(A * u ^ 2 + B * v ^ 2) := by rw [hstationary]; ring

theorem derivation_supported_below_has_no_upper_obstruction :
    ¬ 0 < -(0 : ℝ) := by norm_num

end ConditionalEntropy
