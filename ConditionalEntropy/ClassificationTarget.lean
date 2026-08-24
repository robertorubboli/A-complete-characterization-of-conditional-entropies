import ConditionalEntropy.IntegratedEntropy
import ConditionalEntropy.Moments

/-!
# Closed classification target

This file fixes the exact proposition proved by the final sufficiency and
necessity assembly.  It is deliberately only a definition: no classification
claim is introduced before both directions have been checked.
-/

noncomputable section

open MeasureTheory Set

namespace ConditionalEntropy

/-- Exact four-branch parameter classification for one probability measure on
the compactified Renyi parameter space. -/
def Classifies.{u} (tau : ProbabilityMeasure Param) : Prop :=
  (∀ (t : ℝ) (ht : t ≠ 0),
      CMMonotone (HTemp t ht tau : PolyJointFunctional.{u}) ↔ DBulk t tau) ∧
    (CMMonotone (HMinus tau : PolyJointFunctional.{u}) ↔ DMinus tau) ∧
    (CMMonotone (HPlus tau : PolyJointFunctional.{u}) ↔ tau = diracProb 0) ∧
    (CMMonotone (HZero tau.toFiniteMeasure : PolyJointFunctional.{u}) ↔
      suppMeasure (probMeasure tau) ⊆ Icc (0 : Param) 1)

end ConditionalEntropy
