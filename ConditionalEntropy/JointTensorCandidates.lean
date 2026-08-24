import ConditionalEntropy.CandidateNormalization

/-!
# Tensor algebra of conditional candidates

Active columns of a tensor joint law are exactly pairs of active columns.  The
conditional law on such a column is the tensor of the two conditional laws.
Together with the integrated Renyi tensor identity, this proves tensor
additivity of all four candidate families.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

theorem finMin_comp_equiv {A B : Type u} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] (e : A ≃ B) (f : B → ℝ) :
    finMin (fun a ↦ f (e a)) = finMin f := by
  apply le_antisymm
  · obtain ⟨b, hb⟩ := finMin_mem f
    calc
      finMin (fun a ↦ f (e a)) ≤ f (e (e.symm b)) := finMin_le _ (e.symm b)
      _ = finMin f := by rw [e.apply_symm_apply, hb]
  · obtain ⟨a, ha⟩ := finMin_mem (fun a ↦ f (e a))
    calc
      finMin f ≤ f (e a) := finMin_le f (e a)
      _ = finMin (fun a ↦ f (e a)) := ha

theorem finMax_comp_equiv {A B : Type u} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] (e : A ≃ B) (f : B → ℝ) :
    finMax (fun a ↦ f (e a)) = finMax f := by
  apply le_antisymm
  · obtain ⟨a, ha⟩ := finMax_mem (fun a ↦ f (e a))
    calc
      finMax (fun a ↦ f (e a)) = f (e a) := ha.symm
      _ ≤ finMax f := le_finMax_apply f (e a)
  · obtain ⟨b, hb⟩ := finMax_mem f
    calc
      finMax f = f b := hb.symm
      _ = f (e (e.symm b)) := by rw [e.apply_symm_apply]
      _ ≤ finMax (fun a ↦ f (e a)) :=
        le_finMax_apply (fun a ↦ f (e a)) (e.symm b)

section ActiveTensor

variable {X Y X' Y' : Type u}
variable [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
  [Fintype X'] [Nonempty X'] [Fintype Y'] [Nonempty Y']

omit [Nonempty X] [Nonempty Y] [Nonempty X'] [Nonempty Y'] in
/-- Column masses multiply under a tensor product of joint laws. -/
theorem colMass_jointTensor (P : JointProb X Y) (Q : JointProb X' Y')
    (y : Y) (y' : Y') :
    colMass (jointTensor P Q) (y, y') = colMass P y * colMass Q y' := by
  unfold colMass column l1Mass jointTensor
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]

/-- Left active component of an active tensor column. -/
def tensorActiveLeft (P : JointProb X Y) (Q : JointProb X' Y')
    (z : Active (jointTensor P Q)) : Active P := by
  have hpq : 0 < colMass P z.1.1 * colMass Q z.1.2 := by
    rw [← colMass_jointTensor]
    exact active_colMass_pos (jointTensor P Q) z
  have hq0 : 0 ≤ colMass Q z.1.2 :=
    Finset.sum_nonneg fun x _ ↦ Q.2.1 x z.1.2
  have hp : 0 < colMass P z.1.1 := pos_of_mul_pos_left hpq hq0
  exact ⟨z.1.1, by
    change z.1.1 ∈ Finset.univ.filter (fun y ↦ 0 < colMass P y)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩

/-- Right active component of an active tensor column. -/
def tensorActiveRight (P : JointProb X Y) (Q : JointProb X' Y')
    (z : Active (jointTensor P Q)) : Active Q := by
  have hpq : 0 < colMass P z.1.1 * colMass Q z.1.2 := by
    rw [← colMass_jointTensor]
    exact active_colMass_pos (jointTensor P Q) z
  have hp0 : 0 ≤ colMass P z.1.1 :=
    Finset.sum_nonneg fun x _ ↦ P.2.1 x z.1.1
  have hq : 0 < colMass Q z.1.2 := pos_of_mul_pos_right hpq hp0
  exact ⟨z.1.2, by
    change z.1.2 ∈ Finset.univ.filter (fun y ↦ 0 < colMass Q y)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩⟩

/-- Active tensor columns are canonically equivalent to pairs of active
columns. -/
def activeJointTensorEquiv (P : JointProb X Y) (Q : JointProb X' Y') :
    Active (jointTensor P Q) ≃ Active P × Active Q where
  toFun z := (tensorActiveLeft P Q z, tensorActiveRight P Q z)
  invFun z := ⟨(z.1.1, z.2.1), by
    change (z.1.1, z.2.1) ∈ Finset.univ.filter
      (fun yy ↦ 0 < colMass (jointTensor P Q) yy)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [colMass_jointTensor]
    exact mul_pos (active_colMass_pos P z.1) (active_colMass_pos Q z.2)⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

omit [Nonempty X] [Nonempty Y] [Nonempty X'] [Nonempty Y'] in
@[simp] theorem activeJointTensorEquiv_apply_fst
    (P : JointProb X Y) (Q : JointProb X' Y')
    (z : Active (jointTensor P Q)) :
    (activeJointTensorEquiv P Q z).1.1 = z.1.1 := rfl

omit [Nonempty X] [Nonempty Y] [Nonempty X'] [Nonempty Y'] in
@[simp] theorem activeJointTensorEquiv_apply_snd
    (P : JointProb X Y) (Q : JointProb X' Y')
    (z : Active (jointTensor P Q)) :
    (activeJointTensorEquiv P Q z).2.1 = z.1.2 := rfl

omit [Nonempty Y] [Nonempty Y'] in
/-- Conditional laws tensor on active tensor columns. -/
theorem conditional_jointTensor (P : JointProb X Y) (Q : JointProb X' Y')
    (z : Active (jointTensor P Q)) :
    conditional (jointTensor P Q) z =
      probTensor (conditional P (activeJointTensorEquiv P Q z).1)
        (conditional Q (activeJointTensorEquiv P Q z).2) := by
  apply Subtype.ext
  funext xx
  rw [conditional_apply, colMass_jointTensor]
  change P.1 xx.1 z.1.1 * Q.1 xx.2 z.1.2 /
      (colMass P z.1.1 * colMass Q z.1.2) =
    (P.1 xx.1 z.1.1 / colMass P z.1.1) *
      (Q.1 xx.2 z.1.2 / colMass Q z.1.2)
  have hp := active_colMass_pos P (activeJointTensorEquiv P Q z).1
  have hq := active_colMass_pos Q (activeJointTensorEquiv P Q z).2
  field_simp [hp.ne', hq.ne']

omit [Nonempty X] [Nonempty Y] [Nonempty X'] [Nonempty Y'] in
/-- Reindex any active tensor-column sum by the canonical product equivalence. -/
theorem sum_active_jointTensor (P : JointProb X Y) (Q : JointProb X' Y')
    (f : Active (jointTensor P Q) → ℝ) :
    ∑ z : Active (jointTensor P Q), f z =
      ∑ z : Active P × Active Q, f ((activeJointTensorEquiv P Q).symm z) := by
  exact Fintype.sum_equiv (activeJointTensorEquiv P Q) _ _ (fun _ ↦ rfl)

omit [Nonempty X] [Nonempty Y] [Nonempty X'] [Nonempty Y'] in
@[simp] theorem colMass_jointTensor_equiv_symm
    (P : JointProb X Y) (Q : JointProb X' Y')
    (z : Active P × Active Q) :
    colMass (jointTensor P Q) ((activeJointTensorEquiv P Q).symm z).1 =
      colMass P z.1.1 * colMass Q z.2.1 := by
  change colMass (jointTensor P Q) (z.1.1, z.2.1) = _
  exact colMass_jointTensor P Q z.1.1 z.2.1

omit [Nonempty Y] [Nonempty Y'] in
@[simp] theorem conditional_jointTensor_equiv_symm
    (P : JointProb X Y) (Q : JointProb X' Y')
    (z : Active P × Active Q) :
    conditional (jointTensor P Q) ((activeJointTensorEquiv P Q).symm z) =
      probTensor (conditional P z.1) (conditional Q z.2) := by
  simpa using
    (conditional_jointTensor P Q ((activeJointTensorEquiv P Q).symm z))

end ActiveTensor

section CandidateTensor

variable {X Y X' Y' : Type u}
variable [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
  [Fintype X'] [Nonempty X'] [Fintype Y'] [Nonempty Y']

/-- The exponential temperate sums multiply on joint tensors. -/
theorem temperateSum_jointTensor (t : ℝ) (tau : ProbabilityMeasure Param)
    (P : JointProb X Y) (Q : JointProb X' Y') :
    temperateSum t tau (jointTensor P Q) =
      temperateSum t tau P * temperateSum t tau Q := by
  letI : IsFiniteMeasure (probMeasure tau) := by
    unfold probMeasure
    infer_instance
  unfold temperateSum
  rw [sum_active_jointTensor]
  simp_rw [colMass_jointTensor_equiv_symm, conditional_jointTensor_equiv_symm,
    integratedEntropyPos_tensor]
  simp_rw [mul_add, Real.exp_add]
  rw [Fintype.sum_prod_type]
  calc
    (∑ y : Active P, ∑ y' : Active Q,
        colMass P y.1 * colMass Q y'.1 *
          (Real.exp (t * integratedEntropyPos (probMeasure tau) (conditional P y)) *
            Real.exp (t * integratedEntropyPos (probMeasure tau) (conditional Q y')))) =
      ∑ y : Active P, ∑ y' : Active Q,
        (colMass P y.1 *
          Real.exp (t * integratedEntropyPos (probMeasure tau) (conditional P y))) *
        (colMass Q y'.1 *
          Real.exp (t * integratedEntropyPos (probMeasure tau) (conditional Q y'))) := by
            apply Finset.sum_congr rfl
            intro y _
            apply Finset.sum_congr rfl
            intro y' _
            ring
    _ = _ := (Fintype.sum_mul_sum _ _).symm

/-- Finite-temperature conditional entropy is tensor additive. -/
theorem HTemp_jointTensor (t : ℝ) (ht : t ≠ 0)
    (tau : ProbabilityMeasure Param)
    (P : JointProb X Y) (Q : JointProb X' Y') :
    HTemp t ht tau (jointTensor P Q) = HTemp t ht tau P + HTemp t ht tau Q := by
  unfold HTemp
  rw [temperateSum_jointTensor,
    Real.log_mul (temperateSum_pos t tau P).ne' (temperateSum_pos t tau Q).ne']
  ring

/-- Derivation conditional entropy is tensor additive. -/
theorem HZero_jointTensor (sigma : FiniteMeasure Param)
    (P : JointProb X Y) (Q : JointProb X' Y') :
    HZero sigma (jointTensor P Q) = HZero sigma P + HZero sigma Q := by
  letI : IsFiniteMeasure (finiteMeasure sigma) := by
    unfold finiteMeasure
    infer_instance
  unfold HZero
  rw [sum_active_jointTensor]
  simp_rw [colMass_jointTensor_equiv_symm, conditional_jointTensor_equiv_symm,
    integratedEntropyPos_tensor, mul_add]
  rw [Fintype.sum_prod_type]
  have hP : ∑ y : Active P, colMass P y.1 = 1 := by
    simpa using sum_active_colMass P
  have hQ : ∑ y : Active Q, colMass Q y.1 = 1 := by
    simpa using sum_active_colMass Q
  calc
    (∑ y : Active P, ∑ y' : Active Q,
      (colMass P y.1 * colMass Q y'.1 *
          integratedEntropyPos (finiteMeasure sigma) (conditional P y) +
        colMass P y.1 * colMass Q y'.1 *
          integratedEntropyPos (finiteMeasure sigma) (conditional Q y'))) =
        (∑ y : Active P, colMass P y.1 *
          integratedEntropyPos (finiteMeasure sigma) (conditional P y)) *
            (∑ y' : Active Q, colMass Q y'.1) +
        (∑ y : Active P, colMass P y.1) *
          (∑ y' : Active Q, colMass Q y'.1 *
            integratedEntropyPos (finiteMeasure sigma) (conditional Q y')) := by
              simp_rw [Finset.sum_add_distrib]
              rw [Fintype.sum_mul_sum, Fintype.sum_mul_sum]
              refine congrArg₂ (fun a b : ℝ ↦ a + b) ?_ ?_
              · apply Finset.sum_congr rfl
                intro y _
                apply Finset.sum_congr rfl
                intro y' _
                ring
              · apply Finset.sum_congr rfl
                intro y _
                apply Finset.sum_congr rfl
                intro y' _
                ring
    _ = _ := by rw [hP, hQ]; ring

/-- Negative tropical conditional entropy is tensor additive. -/
theorem HMinus_jointTensor (tau : ProbabilityMeasure Param)
    (P : JointProb X Y) (Q : JointProb X' Y') :
    HMinus tau (jointTensor P Q) = HMinus tau P + HMinus tau Q := by
  letI : IsFiniteMeasure (probMeasure tau) := by
    unfold probMeasure
    infer_instance
  unfold HMinus
  rw [show (fun z : Active (jointTensor P Q) ↦
      integratedEntropyPos (probMeasure tau) (conditional (jointTensor P Q) z)) =
      fun z ↦ integratedEntropyPos (probMeasure tau)
          (conditional P (activeJointTensorEquiv P Q z).1) +
        integratedEntropyPos (probMeasure tau)
          (conditional Q (activeJointTensorEquiv P Q z).2) by
    funext z
    rw [conditional_jointTensor, integratedEntropyPos_tensor]]
  rw [finMin_comp_equiv (activeJointTensorEquiv P Q)
    (fun z : Active P × Active Q ↦
      integratedEntropyPos (probMeasure tau) (conditional P z.1) +
        integratedEntropyPos (probMeasure tau) (conditional Q z.2))]
  exact finMin_prod_add
    (fun y : Active P ↦
      integratedEntropyPos (probMeasure tau) (conditional P y))
    (fun y : Active Q ↦
      integratedEntropyPos (probMeasure tau) (conditional Q y))

/-- Positive tropical conditional entropy is tensor additive. -/
theorem HPlus_jointTensor (tau : ProbabilityMeasure Param)
    (P : JointProb X Y) (Q : JointProb X' Y') :
    HPlus tau (jointTensor P Q) = HPlus tau P + HPlus tau Q := by
  letI : IsFiniteMeasure (probMeasure tau) := by
    unfold probMeasure
    infer_instance
  unfold HPlus
  rw [show (fun z : Active (jointTensor P Q) ↦
      integratedEntropyPos (probMeasure tau) (conditional (jointTensor P Q) z)) =
      fun z ↦ integratedEntropyPos (probMeasure tau)
          (conditional P (activeJointTensorEquiv P Q z).1) +
        integratedEntropyPos (probMeasure tau)
          (conditional Q (activeJointTensorEquiv P Q z).2) by
    funext z
    rw [conditional_jointTensor, integratedEntropyPos_tensor]]
  rw [finMax_comp_equiv (activeJointTensorEquiv P Q)
    (fun z : Active P × Active Q ↦
      integratedEntropyPos (probMeasure tau) (conditional P z.1) +
        integratedEntropyPos (probMeasure tau) (conditional Q z.2))]
  exact finMax_prod_add
    (fun y : Active P ↦
      integratedEntropyPos (probMeasure tau) (conditional P y))
    (fun y : Active Q ↦
      integratedEntropyPos (probMeasure tau) (conditional Q y))

/-- Tensor-additivity packaged at the polymorphic functional level. -/
theorem candidateJointTensorAdditive (t : ℝ) (ht : t ≠ 0)
    (tau : ProbabilityMeasure Param) :
    JointTensorAdditive (HTemp t ht tau) ∧
      JointTensorAdditive (HZero tau.toFiniteMeasure) ∧
      JointTensorAdditive (HMinus tau) ∧
      JointTensorAdditive (HPlus tau) := by
  exact ⟨fun P Q ↦ HTemp_jointTensor t ht tau P Q,
    fun P Q ↦ HZero_jointTensor tau.toFiniteMeasure P Q,
    fun P Q ↦ HMinus_jointTensor tau P Q,
    fun P Q ↦ HPlus_jointTensor tau P Q⟩

end CandidateTensor

end ConditionalEntropy
