import ConditionalEntropy.ParameterConditions
import BoundaryProofs.Stationarity

/-!
# Necessary coefficient conditions

The declarations here are the kernel-checked algebraic conclusions extracted
from the two-block, three-block, and Shannon-point localisers of Section 5.
-/

namespace ConditionalEntropy

theorem positiveTemperate_shannon_atom_zero
    (m : ℝ) (hconcave : ¬ 0 < m ^ 2) : m = 0 := by
  by_contra hm
  exact hconcave (shannon_atom_concavity_obstruction hm)

theorem positiveTemperate_no_upper_moment
    (A : ℝ) (hA_nonpos : A ≤ 0) (hconcave : ¬ 0 < A ^ 2 - A) : A = 0 := by
  rcases hA_nonpos.eq_or_lt with rfl | hA
  · rfl
  · exact False.elim (hconcave (negative_tail_concavity_obstruction hA))

theorem positiveTemperate_lowerMoment_le_one
    (B : ℝ) (hconcave : ¬ 0 < B ^ 2 - B) : B ≤ 1 := by
  by_contra h
  exact hconcave (excessive_lower_moment_concavity_obstruction (lt_of_not_ge h))

theorem negativeTemperate_truncated_moment
    {A C : ℝ} (hA : 0 < A)
    (hconvex : ∀ u v : ℝ, C * u + A * v = 0 → 0 ≤ -(C * u ^ 2 + A * v ^ 2)) :
    C ≤ 0 := by
  by_contra h
  have hC : 0 < C := by linarith
  obtain ⟨hstationary, hnegative⟩ := two_positive_stationary_witness hA hC
  have := hconvex (1 / C) (-1 / A) hstationary
  linarith

theorem negativeTemperate_atMostOneUpperCell
    {A₁ A₂ : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (hconvex : ∀ u v : ℝ, A₁ * u + A₂ * v = 0 →
      0 ≤ -(A₁ * u ^ 2 + A₂ * v ^ 2)) : False := by
  obtain ⟨hstationary, hnegative⟩ := two_positive_stationary_witness hA₂ hA₁
  have := hconvex (1 / A₁) (-1 / A₂) hstationary
  linarith

theorem negativeTropical_moment_nonnegative
    {A C : ℝ} (hA : 0 < A)
    (hquasi : ∀ u v : ℝ, C * u + A * v = 0 → 0 ≤ -(C * u ^ 2 + A * v ^ 2)) :
    C ≤ 0 := by
  by_contra h
  have hC : 0 < C := by linarith
  obtain ⟨hstationary, hnegative⟩ := two_positive_stationary_witness hA hC
  have := hquasi (1 / C) (-1 / A) hstationary
  linarith

theorem derivation_no_positive_upper_tail
    (A : ℝ) (hA : A ≤ 0) (hconcave : ¬ 0 < -A) : A = 0 := by
  rcases hA.eq_or_lt with rfl | hlt
  · rfl
  · exact False.elim (hconcave (positive_tail_derivation_obstruction hlt))

end ConditionalEntropy
