import ConditionalEntropy.IntegratedEntropy

/-!
# Algebra of integrated endpoint-aware Renyi entropy

The pointwise embedding, tensor, and uniform-distribution identities for Renyi
entropy pass through finite positive and signed parameter integrals.  These are
the measure-theoretic identities used by the easy conditional-entropy axioms.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u v

section Positive

variable {I : Type u} {J : Type v}
variable [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]

/-- Zero extension does not change a positive integrated entropy. -/
theorem integratedEntropyPos_zeroExtend (nu : Measure Param) [IsFiniteMeasure nu]
    (e : I ↪ J) (p : ProbVec I) :
    integratedEntropyPos nu (zeroExtendProb e p) = integratedEntropyPos nu p := by
  unfold integratedEntropyPos
  apply integral_congr_ae
  filter_upwards [] with a
  exact renyi_zeroExtend a e p

/-- Integrated Renyi entropy is additive on probability tensors. -/
theorem integratedEntropyPos_tensor (nu : Measure Param) [IsFiniteMeasure nu]
    (p : ProbVec I) (q : ProbVec J) :
    integratedEntropyPos nu (probTensor p q) =
      integratedEntropyPos nu p + integratedEntropyPos nu q := by
  unfold integratedEntropyPos
  rw [show (fun a ↦ renyi a (probTensor p q)) =
      fun a ↦ renyi a p + renyi a q by
    funext a
    exact renyi_tensor a p q]
  exact integral_add (integrable_renyi nu p) (integrable_renyi nu q)

/-- The integrated entropy of a uniform distribution is total parameter mass
times the logarithm of its cardinality. -/
theorem integratedEntropyPos_uniform (nu : Measure Param) [IsFiniteMeasure nu]
    (d : ℕ) (hd : 0 < d) :
    letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    integratedEntropyPos nu (uniformProb (I := Fin d)) =
      nu.real univ * Real.log d := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  unfold integratedEntropyPos
  rw [show (fun a ↦ renyi a (uniformProb (I := Fin d))) =
      fun _ ↦ Real.log d by
    funext a
    exact renyi_uniform d hd a]
  rw [integral_const]
  rfl

/-- Uniform identity on an arbitrary finite nonempty alphabet. -/
theorem integratedEntropyPos_uniformProb (nu : Measure Param) [IsFiniteMeasure nu]
    {K : Type*} [Fintype K] [Nonempty K] :
    integratedEntropyPos nu (uniformProb (I := K)) =
      nu.real univ * Real.log (Fintype.card K : ℝ) := by
  unfold integratedEntropyPos
  rw [show (fun a ↦ renyi a (uniformProb (I := K))) =
      fun _ ↦ Real.log (Fintype.card K : ℝ) by
    funext a
    exact renyi_uniformProb a]
  rw [integral_const]
  rfl

/-- Probability specialization of the uniform identity. -/
theorem integratedEntropyPos_prob_uniform (tau : ProbabilityMeasure Param)
    (d : ℕ) (hd : 0 < d) :
    letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    integratedEntropyPos (probMeasure tau) (uniformProb (I := Fin d)) =
      Real.log d := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  letI : IsFiniteMeasure (probMeasure tau) := by
    unfold probMeasure
    infer_instance
  have h := integratedEntropyPos_uniform (probMeasure tau) d hd
  simpa [probMeasure] using h

/-- Probability specialization on an arbitrary finite nonempty alphabet. -/
theorem integratedEntropyPos_prob_uniformProb (tau : ProbabilityMeasure Param)
    {K : Type*} [Fintype K] [Nonempty K] :
    integratedEntropyPos (probMeasure tau) (uniformProb (I := K)) =
      Real.log (Fintype.card K : ℝ) := by
  letI : IsFiniteMeasure (probMeasure tau) := by
    unfold probMeasure
    infer_instance
  have h := integratedEntropyPos_uniformProb (probMeasure tau) (K := K)
  simpa [probMeasure] using h

end Positive

section Signed

variable {I : Type u} {J : Type v}
variable [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]

/-- Zero extension does not change a signed integrated entropy. -/
theorem integratedEntropySigned_zeroExtend (mu : SignedMeasure Param)
    (e : I ↪ J) (p : ProbVec I) :
    integratedEntropySigned mu (zeroExtendProb e p) =
      integratedEntropySigned mu p := by
  unfold integratedEntropySigned
  apply signedIntegral_congr_ae
  filter_upwards [] with a
  exact renyi_zeroExtend a e p

/-- Signed integrated Renyi entropy is additive on probability tensors. -/
theorem integratedEntropySigned_tensor (mu : SignedMeasure Param)
    (p : ProbVec I) (q : ProbVec J) :
    integratedEntropySigned mu (probTensor p q) =
      integratedEntropySigned mu p + integratedEntropySigned mu q := by
  unfold integratedEntropySigned
  rw [show (fun a ↦ renyi a (probTensor p q)) =
      fun a ↦ renyi a p + renyi a q by
    funext a
    exact renyi_tensor a p q]
  have hp := integrable_renyi_signed_parts mu p
  have hq := integrable_renyi_signed_parts mu q
  exact signedIntegral_add mu hp.1 hp.2 hq.1 hq.2

end Signed

end ConditionalEntropy
