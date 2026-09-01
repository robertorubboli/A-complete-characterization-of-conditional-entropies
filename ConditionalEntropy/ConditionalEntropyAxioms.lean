import ConditionalEntropy.ClassificationTarget

/-!
# Complete conditional-entropy axiom bundle

The complete-proof paper uses natural-log normalization, so an independent
fair bit has value `Real.log 2`.
-/

noncomputable section

namespace ConditionalEntropy

universe u

/-- Universe-polymorphic two-point alphabet. -/
abbrev FairBit.{v} := ULift.{v} (Fin 2)

/-- Nonnegativity on every finite nonempty pair of alphabets. -/
def NonnegativeJointFunctional (F : PolyJointFunctional.{u}) : Prop :=
  ∀ {X Y : Type u}, ∀ [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y],
    ∀ P : JointProb X Y, 0 ≤ F P

/-- Additivity under independent tensor products of joint distributions. -/
def JointTensorAdditive (F : PolyJointFunctional.{u}) : Prop :=
  ∀ {X Y X' Y' : Type u},
    ∀ [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
      [Fintype X'] [Nonempty X'] [Fintype Y'] [Nonempty Y'],
      ∀ (P : JointProb X Y) (Q : JointProb X' Y'),
        F (jointTensor P Q) = F P + F Q

/-- Natural-log normalization on an independent uniform bit. -/
def FairBitNormalized (F : PolyJointFunctional.{u}) : Prop :=
  ∀ {Y : Type u}, ∀ [Fintype Y] [Nonempty Y], ∀ q : ProbVec Y,
    F (independentJoint (uniformProb (I := FairBit.{u})) q) = Real.log 2

/-- Literal conjunction of the five axioms used by the final theorem. -/
def ConditionalEntropyAxioms (F : PolyJointFunctional.{u}) : Prop :=
  NonnegativeJointFunctional F ∧
    JointEmbeddingInvariant F ∧
    JointTensorAdditive F ∧
    FairBitNormalized F ∧
    CEmbedsMonotone F

end ConditionalEntropy
