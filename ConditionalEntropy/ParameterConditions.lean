import BoundaryProofs.Curvature

/-!
# Parameter conditions

Predicates corresponding to equations (247), (248), and (255).  The measure
theory is deliberately separated from the finite coefficient calculus so the
dependency graph mirrors the manuscript.
-/

namespace ConditionalEntropy

/-- Sufficient and necessary positive-temperate coefficient conditions. -/
structure PositiveTemperateProfile where
  shannonAtom : ℝ
  upperMoment : ℝ
  lowerMoment : ℝ

def PositiveTemperateProfile.Admissible (p : PositiveTemperateProfile) : Prop :=
  p.shannonAtom = 0 ∧ p.upperMoment = 0 ∧ p.lowerMoment ≤ 1

/-- Data controlling the exceptional negative-temperate branch. -/
structure NegativeTemperateProfile where
  shannonAtom : ℝ
  lowerMoment : ℝ
  upperMoment : ℝ
  upperSupportCardinality : ℕ

def NegativeTemperateProfile.Admissible (p : NegativeTemperateProfile) : Prop :=
  p.upperSupportCardinality = 0 ∨
    (p.upperSupportCardinality = 1 ∧ p.shannonAtom = 0 ∧ 1 ≤ p.lowerMoment + p.upperMoment)

/-- Data controlling the exceptional negative-tropical branch. -/
structure NegativeTropicalProfile where
  shannonAtom : ℝ
  lowerMoment : ℝ
  upperMoment : ℝ
  upperSupportCardinality : ℕ

def NegativeTropicalProfile.Admissible (p : NegativeTropicalProfile) : Prop :=
  p.upperSupportCardinality = 0 ∨
    (p.upperSupportCardinality = 1 ∧ p.shannonAtom = 0 ∧ 0 ≤ p.lowerMoment + p.upperMoment)

/-- The derivation condition from Proposition 5.8. -/
structure DerivationProfile where
  upperMass : ℝ

def DerivationProfile.Admissible (p : DerivationProfile) : Prop := p.upperMass = 0

end ConditionalEntropy
