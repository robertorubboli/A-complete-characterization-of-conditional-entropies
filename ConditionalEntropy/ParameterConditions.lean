import BoundaryProofs.Curvature

/-!
# Parameter conditions

These predicates record the finite coefficient conditions used by the
sufficiency and necessity arguments.  The measure theory is separated from
the finite coefficient calculus so the dependency graph mirrors the proof
architecture.
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
