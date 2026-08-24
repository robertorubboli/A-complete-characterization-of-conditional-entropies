import ConditionalEntropy.JointTensorCandidates

/-!
# Embedding invariance of the conditional candidates

Zero insertion creates no new active conditioning columns.  The old active
columns are transported bijectively, their masses are unchanged, and their
conditional laws are zero extensions of the original conditional laws.  This
proves embedding invariance for all four endpoint-aware candidates.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

section ZeroExtensionColumns

variable {X Y X' Y' : Type u}
variable [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
  [Fintype X'] [Nonempty X'] [Fintype Y'] [Nonempty Y']

theorem jointZeroExtend_eq_zero_of_not_range_left
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y)
    (x' : X') (y' : Y') (hx : x' ∉ Set.range eX) :
    (jointZeroExtend eX eY P).1 x' y' = 0 := by
  change zeroExtendRaw (prodEmbedding eX eY)
      (fun xy ↦ P.1 xy.1 xy.2) (x', y') = 0
  rw [zeroExtendRaw, dif_neg]
  rintro ⟨xy, hxy⟩
  exact hx ⟨xy.1, congrArg Prod.fst hxy⟩

theorem jointZeroExtend_eq_zero_of_not_range_right
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y)
    (x' : X') (y' : Y') (hy : y' ∉ Set.range eY) :
    (jointZeroExtend eX eY P).1 x' y' = 0 := by
  change zeroExtendRaw (prodEmbedding eX eY)
      (fun xy ↦ P.1 xy.1 xy.2) (x', y') = 0
  rw [zeroExtendRaw, dif_neg]
  rintro ⟨xy, hxy⟩
  exact hy ⟨xy.2, congrArg Prod.snd hxy⟩

/-- An embedded conditioning column has exactly its original mass. -/
@[simp] theorem colMass_jointZeroExtend_image
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y) (y : Y) :
    colMass (jointZeroExtend eX eY P) (eY y) = colMass P y := by
  unfold colMass column l1Mass
  calc
    (∑ x' : X', (jointZeroExtend eX eY P).1 x' (eY y)) =
        ∑ x' : X', zeroExtendRaw eX (fun x ↦ P.1 x y) x' := by
      apply Finset.sum_congr rfl
      intro x' _
      by_cases hx : x' ∈ Set.range eX
      · rcases hx with ⟨x, rfl⟩
        rw [jointZeroExtend_apply, zeroExtendRaw_apply]
      · rw [jointZeroExtend_eq_zero_of_not_range_left eX eY P x' (eY y) hx,
          zeroExtendRaw, dif_neg hx]
    _ = ∑ x : X, P.1 x y := sum_zeroExtendRaw eX (fun x ↦ P.1 x y)

/-- A conditioning column outside the image is identically zero. -/
theorem colMass_jointZeroExtend_of_not_range
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y)
    (y' : Y') (hy : y' ∉ Set.range eY) :
    colMass (jointZeroExtend eX eY P) y' = 0 := by
  unfold colMass column l1Mass
  apply Finset.sum_eq_zero
  intro x' _
  exact jointZeroExtend_eq_zero_of_not_range_right eX eY P x' y' hy

/-- The injection of old active columns into the zero-extended law. -/
def activeJointZeroExtendMap
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y) :
    Active P → Active (jointZeroExtend eX eY P) :=
  fun y ↦ ⟨eY y.1, by
    change eY y.1 ∈ Finset.univ.filter
      (fun z ↦ 0 < colMass (jointZeroExtend eX eY P) z)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by
        rw [colMass_jointZeroExtend_image]
        exact active_colMass_pos P y⟩⟩

theorem activeJointZeroExtendMap_injective
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y) :
    Function.Injective (activeJointZeroExtendMap eX eY P) := by
  intro y z h
  apply Subtype.ext
  exact eY.injective (congrArg Subtype.val h)

theorem activeJointZeroExtendMap_surjective
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y) :
    Function.Surjective (activeJointZeroExtendMap eX eY P) := by
  intro z
  have hzrange : z.1 ∈ Set.range eY := by
    by_contra hzrange
    have hzpos := active_colMass_pos (jointZeroExtend eX eY P) z
    rw [colMass_jointZeroExtend_of_not_range eX eY P z.1 hzrange] at hzpos
    exact (lt_irrefl 0 hzpos)
  rcases hzrange with ⟨y, hy⟩
  have hypos : 0 < colMass P y := by
    rw [← colMass_jointZeroExtend_image eX eY P y, hy]
    exact active_colMass_pos (jointZeroExtend eX eY P) z
  let yA : Active P := ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hypos⟩⟩
  refine ⟨yA, ?_⟩
  apply Subtype.ext
  exact hy

/-- Active columns of a zero extension are canonically equivalent to the old
active columns.  The direction is chosen to simplify finite-sum reindexing. -/
noncomputable def activeJointZeroExtendEquiv
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y) :
    Active (jointZeroExtend eX eY P) ≃ Active P :=
  (Equiv.ofBijective (activeJointZeroExtendMap eX eY P)
    ⟨activeJointZeroExtendMap_injective eX eY P,
      activeJointZeroExtendMap_surjective eX eY P⟩).symm

@[simp] theorem activeJointZeroExtendEquiv_symm_val
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y) (y : Active P) :
    ((activeJointZeroExtendEquiv eX eY P).symm y).1 = eY y.1 := rfl

/-- Conditioning commutes with zero extension on an active image column. -/
@[simp] theorem conditional_jointZeroExtend_image
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y) (y : Active P) :
    conditional (jointZeroExtend eX eY P)
        ((activeJointZeroExtendEquiv eX eY P).symm y) =
      zeroExtendProb eX (conditional P y) := by
  apply Subtype.ext
  funext x'
  by_cases hx : x' ∈ Set.range eX
  · rcases hx with ⟨x, rfl⟩
    rw [conditional_apply, activeJointZeroExtendEquiv_symm_val,
      jointZeroExtend_apply, colMass_jointZeroExtend_image]
    exact (zeroExtendRaw_apply eX (conditional P y).1 x).symm
  · rw [conditional_apply, activeJointZeroExtendEquiv_symm_val,
      jointZeroExtend_eq_zero_of_not_range_left eX eY P x' (eY y.1) hx,
      zero_div]
    change 0 = zeroExtendRaw eX (conditional P y).1 x'
    rw [zeroExtendRaw, dif_neg hx]

@[simp] theorem colMass_jointZeroExtend_equiv_symm
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y) (y : Active P) :
    colMass (jointZeroExtend eX eY P)
        ((activeJointZeroExtendEquiv eX eY P).symm y).1 =
      colMass P y.1 := by
  rw [activeJointZeroExtendEquiv_symm_val,
    colMass_jointZeroExtend_image]

@[simp] theorem integratedEntropyPos_jointZeroExtend_equiv_symm
    (nu : Measure Param) [IsFiniteMeasure nu]
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y) (y : Active P) :
    integratedEntropyPos nu
        (conditional (jointZeroExtend eX eY P)
          ((activeJointZeroExtendEquiv eX eY P).symm y)) =
      integratedEntropyPos nu (conditional P y) := by
  rw [conditional_jointZeroExtend_image,
    integratedEntropyPos_zeroExtend]

/-- Reindex a sum over the active columns of a zero extension. -/
theorem sum_active_jointZeroExtend
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y)
    (f : Active (jointZeroExtend eX eY P) → ℝ) :
    ∑ z : Active (jointZeroExtend eX eY P), f z =
      ∑ y : Active P, f ((activeJointZeroExtendEquiv eX eY P).symm y) := by
  exact Fintype.sum_equiv (activeJointZeroExtendEquiv eX eY P) _ _
    (fun z ↦ by
      rw [(activeJointZeroExtendEquiv eX eY P).symm_apply_apply])

end ZeroExtensionColumns

section CandidateEmbedding

variable {X Y X' Y' : Type u}
variable [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
  [Fintype X'] [Nonempty X'] [Fintype Y'] [Nonempty Y']

theorem temperateSum_jointZeroExtend (t : ℝ) (tau : ProbabilityMeasure Param)
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y) :
    temperateSum t tau (jointZeroExtend eX eY P) = temperateSum t tau P := by
  letI : IsFiniteMeasure (probMeasure tau) := by
    unfold probMeasure
    infer_instance
  unfold temperateSum
  rw [sum_active_jointZeroExtend]
  simp_rw [colMass_jointZeroExtend_equiv_symm,
    integratedEntropyPos_jointZeroExtend_equiv_symm]

theorem HTemp_jointZeroExtend (t : ℝ) (ht : t ≠ 0)
    (tau : ProbabilityMeasure Param)
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y) :
    HTemp t ht tau (jointZeroExtend eX eY P) = HTemp t ht tau P := by
  unfold HTemp
  rw [temperateSum_jointZeroExtend]

theorem HZero_jointZeroExtend (sigma : FiniteMeasure Param)
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y) :
    HZero sigma (jointZeroExtend eX eY P) = HZero sigma P := by
  letI : IsFiniteMeasure (finiteMeasure sigma) := by
    unfold finiteMeasure
    infer_instance
  unfold HZero
  rw [sum_active_jointZeroExtend]
  simp_rw [colMass_jointZeroExtend_equiv_symm,
    integratedEntropyPos_jointZeroExtend_equiv_symm]

theorem integratedEntropyPos_jointZeroExtend_active
    (tau : ProbabilityMeasure Param)
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y)
    (z : Active (jointZeroExtend eX eY P)) :
    integratedEntropyPos (probMeasure tau)
        (conditional (jointZeroExtend eX eY P) z) =
      integratedEntropyPos (probMeasure tau)
        (conditional P (activeJointZeroExtendEquiv eX eY P z)) := by
  letI : IsFiniteMeasure (probMeasure tau) := by
    unfold probMeasure
    infer_instance
  let e := activeJointZeroExtendEquiv eX eY P
  calc
    integratedEntropyPos (probMeasure tau)
        (conditional (jointZeroExtend eX eY P) z) =
      integratedEntropyPos (probMeasure tau)
        (conditional (jointZeroExtend eX eY P) (e.symm (e z))) := by
          rw [e.symm_apply_apply]
    _ = integratedEntropyPos (probMeasure tau)
        (conditional P (e z)) := by
          exact integratedEntropyPos_jointZeroExtend_equiv_symm
            (probMeasure tau) eX eY P (e z)

theorem HMinus_jointZeroExtend (tau : ProbabilityMeasure Param)
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y) :
    HMinus tau (jointZeroExtend eX eY P) = HMinus tau P := by
  unfold HMinus
  rw [show (fun z : Active (jointZeroExtend eX eY P) ↦
      integratedEntropyPos (probMeasure tau)
        (conditional (jointZeroExtend eX eY P) z)) =
      fun z ↦ integratedEntropyPos (probMeasure tau)
        (conditional P (activeJointZeroExtendEquiv eX eY P z)) by
    funext z
    exact integratedEntropyPos_jointZeroExtend_active tau eX eY P z]
  exact finMin_comp_equiv (activeJointZeroExtendEquiv eX eY P)
    (fun y : Active P ↦
      integratedEntropyPos (probMeasure tau) (conditional P y))

theorem HPlus_jointZeroExtend (tau : ProbabilityMeasure Param)
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y) :
    HPlus tau (jointZeroExtend eX eY P) = HPlus tau P := by
  unfold HPlus
  rw [show (fun z : Active (jointZeroExtend eX eY P) ↦
      integratedEntropyPos (probMeasure tau)
        (conditional (jointZeroExtend eX eY P) z)) =
      fun z ↦ integratedEntropyPos (probMeasure tau)
        (conditional P (activeJointZeroExtendEquiv eX eY P z)) by
    funext z
    exact integratedEntropyPos_jointZeroExtend_active tau eX eY P z]
  exact finMax_comp_equiv (activeJointZeroExtendEquiv eX eY P)
    (fun y : Active P ↦
      integratedEntropyPos (probMeasure tau) (conditional P y))

/-- Embedding invariance of all four candidate families. -/
theorem candidateJointEmbeddingInvariant (t : ℝ) (ht : t ≠ 0)
    (tau : ProbabilityMeasure Param) :
    JointEmbeddingInvariant (HTemp t ht tau) ∧
      JointEmbeddingInvariant (HZero tau.toFiniteMeasure) ∧
      JointEmbeddingInvariant (HMinus tau) ∧
      JointEmbeddingInvariant (HPlus tau) := by
  exact ⟨fun eX eY P ↦ HTemp_jointZeroExtend t ht tau eX eY P,
    fun eX eY P ↦ HZero_jointZeroExtend tau.toFiniteMeasure eX eY P,
    fun eX eY P ↦ HMinus_jointZeroExtend tau eX eY P,
    fun eX eY P ↦ HPlus_jointZeroExtend tau eX eY P⟩

end CandidateEmbedding

end ConditionalEntropy
