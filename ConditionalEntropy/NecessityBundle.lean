import ConditionalEntropy.DerivationNecessity
import ConditionalEntropy.NegativeNecessity
import ConditionalEntropy.NegativeTropicalNecessity
import ConditionalEntropy.PositiveNecessity
import ConditionalEntropy.PositiveTropicalNecessity
import ConditionalEntropy.ShapeReduction

/-!
# Final necessity assembly

This module combines the five branch-specific necessity theorems into the
literal four-way conjunction used by the closed classification target.
-/

noncomputable section

open MeasureTheory Set

namespace ConditionalEntropy

universe u

/- This wrapper keeps the final assembly's use of the public
negative-tropical necessity theorem explicit and local. -/
private theorem negativeTropicalNecessityForBundle
    (tau : ProbabilityMeasure Param) :
    CMMonotone (HMinus tau : PolyJointFunctional.{u}) → DMinus tau :=
  negativeTropicalNecessity tau

private theorem derivationProbabilityNecessity
    (tau : ProbabilityMeasure Param) :
    CMMonotone
        (HZero tau.toFiniteMeasure : PolyJointFunctional.{u}) →
      suppMeasure (probMeasure tau) ⊆ Icc (0 : Param) 1 := by
  intro hmono
  have hconc :
      ∀ {I : Type u} [Fintype I] [Nonempty I],
        ConcaveCone
          (derivationColumn tau.toFiniteMeasure : ConeVec I → ℝ) :=
    ((globalTemperateDerivationShapeReduction
      1 tau tau.toFiniteMeasure).2.2).1 hmono
  have hsupp := derivationNecessity tau.toFiniteMeasure hconc
  simpa only [finiteMeasure, probMeasure,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure] using hsupp

/-- All necessary parameter conditions for the four conditional-entropy
candidate branches. -/
theorem necessityBundle (tau : ProbabilityMeasure Param) :
    (∀ (t : ℝ) (ht : t ≠ 0),
      CMMonotone
          (HTemp t ht tau : PolyJointFunctional.{u}) →
        DBulk t tau) ∧
    (CMMonotone
        (HMinus tau : PolyJointFunctional.{u}) →
      DMinus tau) ∧
    (CMMonotone
        (HPlus tau : PolyJointFunctional.{u}) →
      tau = diracProb 0) ∧
    (CMMonotone
        (HZero tau.toFiniteMeasure : PolyJointFunctional.{u}) →
      suppMeasure (probMeasure tau) ⊆ Icc (0 : Param) 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht hmono
    rcases lt_or_gt_of_ne ht with htneg | htpos
    · rcases negativeTemperateProbabilityNecessity tau t htneg hmono with
        hlower | ⟨astar, hexc⟩
      · exact Or.inr (Or.inl hlower)
      · exact Or.inr (Or.inr ⟨astar, hexc⟩)
    · exact Or.inl
        (positiveTemperateProbabilityNecessity tau t htpos hmono)
  · exact negativeTropicalNecessityForBundle tau
  · exact positiveTropicalNecessity tau
  · exact derivationProbabilityNecessity tau

end ConditionalEntropy
