import ConditionalEntropy.Sufficient
import ConditionalEntropy.Necessary

/-!
# Paper-facing assembly

This module assembles the independently checked curvature and stationarity
calculations into the necessary/sufficient parameter tests used by the
replacement Sections 4 and 5.
-/

namespace ConditionalEntropy

/-- Positive-temperate necessity, corresponding to Proposition 5.1. -/
theorem positiveTemperate_necessary
    (p : PositiveTemperateProfile)
    (hShannon : ¬ 0 < p.shannonAtom ^ 2)
    (hUpperSign : p.upperMoment ≤ 0)
    (hUpper : ¬ 0 < p.upperMoment ^ 2 - p.upperMoment)
    (hLower : ¬ 0 < p.lowerMoment ^ 2 - p.lowerMoment) :
    p.Admissible := by
  refine ⟨positiveTemperate_shannon_atom_zero p.shannonAtom hShannon,
    positiveTemperate_no_upper_moment p.upperMoment hUpperSign hUpper, ?_⟩
  exact positiveTemperate_lowerMoment_le_one p.lowerMoment hLower

/-- The exceptional negative-temperate moment inequality from Propositions
5.2--5.3. -/
theorem negativeTemperate_exceptional_moment
    {lower upper : ℝ} (hupper : 0 < upper)
    (hconvex : ∀ u v : ℝ, (1 - upper - lower) * u + upper * v = 0 →
      0 ≤ -((1 - upper - lower) * u ^ 2 + upper * v ^ 2)) :
    1 ≤ lower + upper := by
  have h := negativeTemperate_truncated_moment hupper hconvex
  linarith

/-- The exceptional negative-tropical moment inequality, equation (255) after
normalizing the negative measure. -/
theorem negativeTropical_exceptional_moment
    {lower upper : ℝ} (hupper : 0 < upper)
    (hquasi : ∀ u v : ℝ, (-upper - lower) * u + upper * v = 0 →
      0 ≤ -((-upper - lower) * u ^ 2 + upper * v ^ 2)) :
    0 ≤ lower + upper := by
  have h := negativeTropical_moment_nonnegative hupper hquasi
  linarith

/-- Derivation necessity, corresponding to Proposition 5.7. -/
theorem derivation_necessary (p : DerivationProfile)
    (hUpperSign : p.upperMass ≤ 0) (hconcave : ¬ 0 < -p.upperMass) :
    p.Admissible :=
  derivation_no_positive_upper_tail p.upperMass hUpperSign hconcave

end ConditionalEntropy
