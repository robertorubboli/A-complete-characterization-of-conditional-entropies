import ConditionalEntropy.ClassificationTarget
import ConditionalEntropy.NecessityBundle
import ConditionalEntropy.Section4Sufficiency

/-!
# Complete parameter classification

The four fields below pair the already established sufficiency theorems with
the corresponding fields of `necessityBundle`.
-/

noncomputable section

open MeasureTheory Set

namespace ConditionalEntropy

universe u

/-- Every probability parameter has exactly the finite-temperature,
negative-tropical, positive-tropical, and derivation ranges stated by
`Classifies`. -/
theorem mainClassification (tau : ProbabilityMeasure Param) :
    Classifies.{u} tau := by
  unfold Classifies
  have hnec := necessityBundle.{u} tau
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    constructor
    · exact hnec.1 t ht
    · intro hbulk
      have hsuff : CMMonotone
          (HTemp t (DBulk.ne hbulk) tau : PolyJointFunctional.{u}) :=
        finiteTSufficiency tau t hbulk
      have hne : DBulk.ne hbulk = ht := Subsingleton.elim _ _
      rw [hne] at hsuff
      intro X Y Y' _ _ _ _ _ _ P Q hPQ
      exact hsuff P Q hPQ
  · constructor
    · exact hnec.2.1
    · exact negativeTropicalSufficiency tau
  · constructor
    · exact hnec.2.2.1
    · intro heq
      subst tau
      exact positiveTropicalSufficiency
  · constructor
    · exact hnec.2.2.2
    · intro hsupp
      have hder :
          CMMonotone
              (derivationFamily tau.toFiniteMeasure : PolyJointFunctional.{u}) ∧
            (derivationFamily tau.toFiniteMeasure : PolyJointFunctional.{u}) =
              (HZero tau.toFiniteMeasure : PolyJointFunctional.{u}) :=
        derivationSufficiency tau.toFiniteMeasure hsupp
      intro X Y Y' _ _ _ _ _ _ P Q hPQ
      have hmono := hder.1 P Q hPQ
      rw [hder.2] at hmono
      exact hmono

end ConditionalEntropy
