import ConditionalEntropy.ConditionalEntropyAxioms
import ConditionalEntropy.IntegratedEntropyAlgebra
import ConditionalEntropy.FiniteExtrema

/-!
# Fair-bit normalization of all four candidate families

For an independent joint law every active conditioning column has the same
conditional distribution.  This makes the normalization calculation uniform
across the temperate, derivation, and two tropical candidates.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

private theorem independentConditional_active
    {X Y : Type u} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (p : ProbVec X) (q : ProbVec Y)
    (y : Active (independentJoint p q)) :
    conditional (independentJoint p q) y = p := by
  have hy : 0 < q.1 y.1 := by
    simpa [independentColumnMass] using active_colMass_pos (independentJoint p q) y
  have heq : y = independentActive p q y.1 hy := by
    apply Subtype.ext
    rfl
  rw [heq]
  exact independentConditional p q y.1 hy

theorem sum_active_colMass
    {X Y : Type u} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (P : JointProb X Y) :
    ∑ y : Active P, colMass P y.1 = 1 := by
  classical
  calc
    ∑ y : Active P, colMass P y.1 =
        ∑ y ∈ activeFinset P, colMass P y :=
      (Finset.sum_subtype (activeFinset P) (fun _ ↦ Iff.rfl)
        (fun y ↦ colMass P y)).symm
    _ = 1 := (positiveColumnsNonempty P).2

/-- Exact finite-temperature normalization on an independent uniform bit. -/
theorem HTemp_independent_uniform_bit (t : ℝ) (ht : t ≠ 0)
    (tau : ProbabilityMeasure Param)
    {Y : Type u} [Fintype Y] [Nonempty Y] (q : ProbVec Y) :
    HTemp t ht tau
      (independentJoint (uniformProb (I := FairBit.{u})) q) = Real.log 2 := by
  let P := independentJoint (uniformProb (I := FairBit.{u})) q
  have hA : ∀ y : Active P,
      integratedEntropyPos (probMeasure tau) (conditional P y) = Real.log 2 := by
    intro y
    rw [show conditional P y = uniformProb (I := FairBit.{u}) by
      exact independentConditional_active (uniformProb (I := FairBit.{u})) q y]
    simpa using integratedEntropyPos_prob_uniformProb tau (K := FairBit.{u})
  have hsum : temperateSum t tau P = Real.exp (t * Real.log 2) := by
    unfold temperateSum
    simp_rw [hA]
    rw [← Finset.sum_mul, sum_active_colMass P, one_mul]
  unfold HTemp
  rw [hsum, Real.log_exp]
  field_simp [ht]

/-- Exact derivation normalization for a probability parameter measure. -/
theorem HZero_independent_uniform_bit (tau : ProbabilityMeasure Param)
    {Y : Type u} [Fintype Y] [Nonempty Y] (q : ProbVec Y) :
    HZero tau.toFiniteMeasure
      (independentJoint (uniformProb (I := FairBit.{u})) q) = Real.log 2 := by
  let P := independentJoint (uniformProb (I := FairBit.{u})) q
  have hA : ∀ y : Active P,
      integratedEntropyPos (finiteMeasure tau.toFiniteMeasure) (conditional P y) =
        Real.log 2 := by
    intro y
    rw [show conditional P y = uniformProb (I := FairBit.{u}) by
      exact independentConditional_active (uniformProb (I := FairBit.{u})) q y]
    have h := integratedEntropyPos_prob_uniformProb tau (K := FairBit.{u})
    simpa [finiteMeasure, probMeasure] using h
  unfold HZero
  change (∑ y : Active P, colMass P y.1 *
    integratedEntropyPos (finiteMeasure tau.toFiniteMeasure) (conditional P y)) = _
  simp_rw [hA]
  rw [← Finset.sum_mul, sum_active_colMass P, one_mul]

/-- Exact negative-tropical normalization on an independent uniform bit. -/
theorem HMinus_independent_uniform_bit (tau : ProbabilityMeasure Param)
    {Y : Type u} [Fintype Y] [Nonempty Y] (q : ProbVec Y) :
    HMinus tau (independentJoint (uniformProb (I := FairBit.{u})) q) = Real.log 2 := by
  let P := independentJoint (uniformProb (I := FairBit.{u})) q
  unfold HMinus
  letI : Nonempty (Active P) := activeNonempty P
  change finMin (fun y : Active P ↦
    integratedEntropyPos (probMeasure tau) (conditional P y)) = _
  have hconst : (fun y : Active P ↦
      integratedEntropyPos (probMeasure tau) (conditional P y)) =
      fun _ ↦ Real.log 2 := by
    funext y
    rw [independentConditional_active (uniformProb (I := FairBit.{u})) q y]
    simpa using integratedEntropyPos_prob_uniformProb tau (K := FairBit.{u})
  rw [hconst]
  obtain ⟨y, hy⟩ := finMin_mem (fun _ : Active P ↦ Real.log 2)
  exact hy.symm

/-- Exact positive-tropical normalization on an independent uniform bit. -/
theorem HPlus_independent_uniform_bit (tau : ProbabilityMeasure Param)
    {Y : Type u} [Fintype Y] [Nonempty Y] (q : ProbVec Y) :
    HPlus tau (independentJoint (uniformProb (I := FairBit.{u})) q) = Real.log 2 := by
  let P := independentJoint (uniformProb (I := FairBit.{u})) q
  unfold HPlus
  letI : Nonempty (Active P) := activeNonempty P
  change finMax (fun y : Active P ↦
    integratedEntropyPos (probMeasure tau) (conditional P y)) = _
  have hconst : (fun y : Active P ↦
      integratedEntropyPos (probMeasure tau) (conditional P y)) =
      fun _ ↦ Real.log 2 := by
    funext y
    rw [independentConditional_active (uniformProb (I := FairBit.{u})) q y]
    simpa using integratedEntropyPos_prob_uniformProb tau (K := FairBit.{u})
  rw [hconst]
  obtain ⟨y, hy⟩ := finMax_mem (fun _ : Active P ↦ Real.log 2)
  exact hy.symm

/-- The four exact `FairBitNormalized` clauses. -/
theorem candidateFairBitNormalization (t : ℝ) (ht : t ≠ 0)
    (tau : ProbabilityMeasure Param) :
    FairBitNormalized (HTemp t ht tau) ∧
      FairBitNormalized (HZero tau.toFiniteMeasure) ∧
      FairBitNormalized (HMinus tau) ∧
      FairBitNormalized (HPlus tau) := by
  exact ⟨fun q ↦ HTemp_independent_uniform_bit t ht tau q,
    fun q ↦ HZero_independent_uniform_bit tau q,
    fun q ↦ HMinus_independent_uniform_bit tau q,
    fun q ↦ HPlus_independent_uniform_bit tau q⟩

/-- Nonnegativity of the four candidate families, packaged at the polymorphic
joint-functional level. -/
theorem candidateNonnegative (t : ℝ) (ht : t ≠ 0)
    (tau : ProbabilityMeasure Param) :
    NonnegativeJointFunctional (HTemp t ht tau) ∧
      NonnegativeJointFunctional (HZero tau.toFiniteMeasure) ∧
      NonnegativeJointFunctional (HMinus tau) ∧
      NonnegativeJointFunctional (HPlus tau) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y _ _ _ _ P
    exact (conditionalCandidates_nonneg P tau tau.toFiniteMeasure t ht).2.1
  · intro X Y _ _ _ _ P
    exact (conditionalCandidates_nonneg P tau tau.toFiniteMeasure t ht).2.2.1
  · intro X Y _ _ _ _ P
    exact (conditionalCandidates_nonneg P tau tau.toFiniteMeasure t ht).2.2.2.1
  · intro X Y _ _ _ _ P
    exact (conditionalCandidates_nonneg P tau tau.toFiniteMeasure t ht).2.2.2.2

end ConditionalEntropy
