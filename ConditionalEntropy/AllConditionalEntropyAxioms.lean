import ConditionalEntropy.CandidateNormalization
import ConditionalEntropy.CandidateEmbeddingInvariance
import ConditionalEntropy.JointTensorCandidates
import ConditionalEntropy.ConditionalEntropyAxioms
import ConditionalEntropy.Section4Sufficiency

/-!
# The complete axiom bundle for every admissible candidate

The difficult order clauses are supplied by Section 4.  The remaining four
axioms are the candidate normalization, embedding, tensor, and nonnegativity
packages, and fixed-row monotonicity is lifted to the embedded relation by
`embeddingLift`.
-/

noncomputable section

open MeasureTheory Set

namespace ConditionalEntropy

universe u

/-- Every admissible member of the four candidate families satisfies the
literal five-part conditional-entropy axiom bundle
(`cor:all-conditional-entropy-axioms`). -/
theorem allConditionalEntropyAxioms :
    (∀ (t : ℝ) (tau : ProbabilityMeasure Param),
      ∀ h : DBulk t tau,
        ConditionalEntropyAxioms
          (HTemp t (DBulk.ne h) tau : PolyJointFunctional.{u})) ∧
    (∀ tau : ProbabilityMeasure Param, DMinus tau →
      ConditionalEntropyAxioms
        (HMinus tau : PolyJointFunctional.{u})) ∧
    ConditionalEntropyAxioms
      (HPlus (diracProb 0) : PolyJointFunctional.{u}) ∧
    (∀ tau : ProbabilityMeasure Param,
      suppMeasure (probMeasure tau) ⊆ Icc (0 : Param) 1 →
        ConditionalEntropyAxioms
          (HZero tau.toFiniteMeasure : PolyJointFunctional.{u})) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t tau h
    let ht : t ≠ 0 := DBulk.ne h
    have hnon : NonnegativeJointFunctional
        (HTemp t ht tau : PolyJointFunctional.{u}) :=
      (candidateNonnegative.{u, u, u, u} t ht tau).1
    have hinv : JointEmbeddingInvariant
        (HTemp t ht tau : PolyJointFunctional.{u}) :=
      (candidateJointEmbeddingInvariant.{u, u, u, u} t ht tau).1
    have htensor : JointTensorAdditive
        (HTemp t ht tau : PolyJointFunctional.{u}) :=
      (candidateJointTensorAdditive.{u, u, u, u} t ht tau).1
    have hnorm : FairBitNormalized
        (HTemp t ht tau : PolyJointFunctional.{u}) :=
      (candidateFairBitNormalization.{u, u, u, u} t ht tau).1
    have hmono : CMMonotone
        (HTemp t ht tau : PolyJointFunctional.{u}) :=
      finiteTSufficiency tau t h
    change ConditionalEntropyAxioms
      (HTemp t ht tau : PolyJointFunctional.{u})
    exact ⟨hnon, hinv, htensor, hnorm,
      embeddingLift _ hinv hmono⟩
  · intro tau hAdm
    let t : ℝ := 1
    have ht : t ≠ 0 := one_ne_zero
    have hnon : NonnegativeJointFunctional
        (HMinus tau : PolyJointFunctional.{u}) :=
      (candidateNonnegative.{u, u, u, u} t ht tau).2.2.1
    have hinv : JointEmbeddingInvariant
        (HMinus tau : PolyJointFunctional.{u}) :=
      (candidateJointEmbeddingInvariant.{u, u, u, u} t ht tau).2.2.1
    have htensor : JointTensorAdditive
        (HMinus tau : PolyJointFunctional.{u}) :=
      (candidateJointTensorAdditive.{u, u, u, u} t ht tau).2.2.1
    have hnorm : FairBitNormalized
        (HMinus tau : PolyJointFunctional.{u}) :=
      (candidateFairBitNormalization.{u, u, u, u} t ht tau).2.2.1
    have hmono : CMMonotone
        (HMinus tau : PolyJointFunctional.{u}) :=
      negativeTropicalSufficiency tau hAdm
    exact ⟨hnon, hinv, htensor, hnorm,
      embeddingLift _ hinv hmono⟩
  · let tau := diracProb 0
    let t : ℝ := 1
    have ht : t ≠ 0 := one_ne_zero
    have hnon : NonnegativeJointFunctional
        (HPlus tau : PolyJointFunctional.{u}) :=
      (candidateNonnegative.{u, u, u, u} t ht tau).2.2.2
    have hinv : JointEmbeddingInvariant
        (HPlus tau : PolyJointFunctional.{u}) :=
      (candidateJointEmbeddingInvariant.{u, u, u, u} t ht tau).2.2.2
    have htensor : JointTensorAdditive
        (HPlus tau : PolyJointFunctional.{u}) :=
      (candidateJointTensorAdditive.{u, u, u, u} t ht tau).2.2.2
    have hnorm : FairBitNormalized
        (HPlus tau : PolyJointFunctional.{u}) :=
      (candidateFairBitNormalization.{u, u, u, u} t ht tau).2.2.2
    have hmono : CMMonotone
        (HPlus tau : PolyJointFunctional.{u}) :=
      positiveTropicalSufficiency
    exact ⟨hnon, hinv, htensor, hnorm,
      embeddingLift _ hinv hmono⟩
  · intro tau hsupp
    let t : ℝ := 1
    have ht : t ≠ 0 := one_ne_zero
    have hnon : NonnegativeJointFunctional
        (HZero tau.toFiniteMeasure : PolyJointFunctional.{u}) :=
      (candidateNonnegative.{u, u, u, u} t ht tau).2.1
    have hinv : JointEmbeddingInvariant
        (HZero tau.toFiniteMeasure : PolyJointFunctional.{u}) :=
      (candidateJointEmbeddingInvariant.{u, u, u, u} t ht tau).2.1
    have htensor : JointTensorAdditive
        (HZero tau.toFiniteMeasure : PolyJointFunctional.{u}) :=
      (candidateJointTensorAdditive.{u, u, u, u} t ht tau).2.1
    have hnorm : FairBitNormalized
        (HZero tau.toFiniteMeasure : PolyJointFunctional.{u}) :=
      (candidateFairBitNormalization.{u, u, u, u} t ht tau).2.1
    have hder :
        CMMonotone
            (derivationFamily tau.toFiniteMeasure : PolyJointFunctional.{u}) ∧
          (derivationFamily tau.toFiniteMeasure : PolyJointFunctional.{u}) =
            (HZero tau.toFiniteMeasure : PolyJointFunctional.{u}) :=
      derivationSufficiency tau.toFiniteMeasure hsupp
    have hmono : CMMonotone
        (HZero tau.toFiniteMeasure : PolyJointFunctional.{u}) := by
      rw [← hder.2]
      exact hder.1
    exact ⟨hnon, hinv, htensor, hnorm,
      embeddingLift _ hinv hmono⟩

end ConditionalEntropy
