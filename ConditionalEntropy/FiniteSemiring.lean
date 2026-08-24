import ConditionalEntropy.FiniteData
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Sum

/-!
# Finite representatives of the conditional-majorization semiring

The semiring in the manuscript consists of unnormalised finite nonnegative
matrices, modulo relabelling and insertion or deletion of zero rows and
columns.  This file formalises the representative-level algebra.  The
heterogeneous direct sum and tensor product deliberately retain their finite
row and column types; quotienting by zero embeddings is a separate step.
-/

open scoped BigOperators

namespace ConditionalEntropy

universe u v w z

/-- An unnormalised finite joint distribution: a matrix with nonnegative
entries.  This is the representative carrier used by the manuscript's
conditional-majorization semiring. -/
def JointCone (X : Type u) (Y : Type v) :=
  {P : X → Y → ℝ // ∀ x y, 0 ≤ P x y}

instance {X : Type u} {Y : Type v} : CoeFun (JointCone X Y) (fun _ => X → Y → ℝ) :=
  ⟨fun P => P.1⟩

/-- Total mass of an unnormalised joint matrix. -/
noncomputable def jointConeMass {X : Type u} {Y : Type v}
    [Fintype X] [Fintype Y] (P : JointCone X Y) : ℝ :=
  ∑ x, ∑ y, P x y

/-- Block-diagonal direct sum of finite nonnegative matrices. -/
def jointConeDirectSum {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    (P : JointCone X Y) (Q : JointCone X' Y') :
    JointCone (Sum X X') (Sum Y Y') :=
  ⟨fun x y => match x, y with
    | Sum.inl x, Sum.inl y => P x y
    | Sum.inr x, Sum.inr y => Q x y
    | _, _ => 0,
   by
    intro x y
    cases x with
    | inl x =>
        cases y with
        | inl y => exact P.2 x y
        | inr _ => exact le_rfl
    | inr x =>
        cases y with
        | inl _ => exact le_rfl
        | inr y => exact Q.2 x y⟩

/-- Kronecker product of finite nonnegative matrices. -/
def jointConeTensor {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    (P : JointCone X Y) (Q : JointCone X' Y') :
    JointCone (X × X') (Y × Y') :=
  ⟨fun x y => P x.1 y.1 * Q x.2 y.2,
   fun x y => mul_nonneg (P.2 x.1 y.1) (Q.2 x.2 y.2)⟩

/-- The representative of the additive zero. -/
def jointConeZero : JointCone (Fin 1) (Fin 1) :=
  ⟨fun _ _ => 0, fun _ _ => le_rfl⟩

/-- The representative of the multiplicative unit. -/
def jointConeOne : JointCone (Fin 1) (Fin 1) :=
  ⟨fun _ _ => 1, fun _ _ => zero_le_one⟩

/-- Relabel both alphabets by equivalences. -/
def jointConeRelabel {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    (eX : X ≃ X') (eY : Y ≃ Y') (P : JointCone X Y) : JointCone X' Y' :=
  ⟨fun x y => P (eX.symm x) (eY.symm y),
   fun x y => P.2 (eX.symm x) (eY.symm y)⟩

/-- Product of finite embeddings, used for joint zero extension. -/
def jointConeProdEmbedding {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    (eX : X ↪ X') (eY : Y ↪ Y') : X × Y ↪ X' × Y' :=
  ⟨fun p => (eX p.1, eY p.2), by
    intro a b h
    exact Prod.ext (eX.injective (congrArg Prod.fst h))
      (eY.injective (congrArg Prod.snd h))⟩

/-- Canonical injection into the left summand. -/
def sumInlEmbedding (X : Type u) (Z : Type v) : X ↪ Sum X Z :=
  ⟨Sum.inl, fun _ _ h => Sum.inl.inj h⟩

/-- Canonical injection into the right summand. -/
def sumInrEmbedding (X : Type u) (Z : Type v) : Z ↪ Sum X Z :=
  ⟨Sum.inr, fun _ _ h => Sum.inr.inj h⟩

/-- A raw zero extension preserves the sum of a finite family. -/
theorem sum_zeroExtendRaw {I : Type u} {J : Type v}
    [Fintype I] [Fintype J] (e : I ↪ J) (x : I → ℝ) :
    ∑ j, zeroExtendRaw e x j = ∑ i, x i := by
  classical
  calc
    ∑ j : J, zeroExtendRaw e x j =
        ∑ j ∈ Finset.univ.map e, zeroExtendRaw e x j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have hrange : j ∉ Set.range e := by
        rintro ⟨i, rfl⟩
        exact hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      rw [zeroExtendRaw, dif_neg hrange]
    _ = ∑ i : I, x i := by simp

/-- Insert zero rows and columns into an unnormalized finite joint matrix. -/
noncomputable def jointConeZeroExtend
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointCone X Y) : JointCone X' Y' :=
  ⟨fun x y => zeroExtendRaw (jointConeProdEmbedding eX eY)
      (fun xy => P.1 xy.1 xy.2) (x, y), by
    intro x y
    classical
    change 0 ≤ zeroExtendRaw (jointConeProdEmbedding eX eY)
      (fun xy => P.1 xy.1 xy.2) (x, y)
    unfold zeroExtendRaw
    split <;> rename_i h
    · exact P.2 (Classical.choose h).1 (Classical.choose h).2
    · exact le_rfl⟩

@[simp] theorem jointConeZeroExtend_apply
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointCone X Y) (x : X) (y : Y) :
    jointConeZeroExtend eX eY P (eX x) (eY y) = P x y := by
  change zeroExtendRaw (jointConeProdEmbedding eX eY)
      (fun xy => P.1 xy.1 xy.2) (eX x, eY y) = P.1 x y
  simpa [jointConeProdEmbedding] using
    (zeroExtendRaw_apply (jointConeProdEmbedding eX eY)
      (fun xy => P.1 xy.1 xy.2) (x, y))

/-- Zero insertion preserves the total mass of an unnormalized matrix. -/
@[simp] theorem jointConeMass_zeroExtend
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointCone X Y) :
    jointConeMass (jointConeZeroExtend eX eY P) = jointConeMass P := by
  calc
    jointConeMass (jointConeZeroExtend eX eY P) =
        ∑ xy : X' × Y', zeroExtendRaw (jointConeProdEmbedding eX eY)
          (fun p => P.1 p.1 p.2) xy := by
      simp only [jointConeMass, jointConeZeroExtend, Fintype.sum_prod_type]
    _ = ∑ xy : X × Y, P.1 xy.1 xy.2 :=
      sum_zeroExtendRaw (jointConeProdEmbedding eX eY) (fun p => P.1 p.1 p.2)
    _ = jointConeMass P := by
      simp only [jointConeMass, Fintype.sum_prod_type]

/-- Zero extension along equivalences is exactly relabelling. -/
theorem jointConeZeroExtend_equiv
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (eX : X ≃ X') (eY : Y ≃ Y') (P : JointCone X Y) :
    jointConeZeroExtend eX.toEmbedding eY.toEmbedding P = jointConeRelabel eX eY P := by
  apply Subtype.ext
  funext x' y'
  obtain ⟨x, rfl⟩ := eX.surjective x'
  obtain ⟨y, rfl⟩ := eY.surjective y'
  change zeroExtendRaw (jointConeProdEmbedding eX.toEmbedding eY.toEmbedding)
      (fun xy => P.1 xy.1 xy.2) (eX x, eY y) =
    P.1 (eX.symm (eX x)) (eY.symm (eY y))
  calc
    _ = P.1 x y := by
      simpa [jointConeProdEmbedding] using
        (zeroExtendRaw_apply (jointConeProdEmbedding eX.toEmbedding eY.toEmbedding)
          (fun xy => P.1 xy.1 xy.2) (x, y))
    _ = _ := by simp

/-- Adding an all-zero block is exactly simultaneous zero extension of the
row and column alphabets. -/
theorem jointConeZeroExtend_sumInl
    {X : Type u} {Y : Type v} {Z : Type w} {W : Type z}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype W]
    (P : JointCone X Y) :
    jointConeZeroExtend (sumInlEmbedding X Z) (sumInlEmbedding Y W) P =
      jointConeDirectSum P (⟨fun _ _ => 0, fun _ _ => le_rfl⟩ : JointCone Z W) := by
  apply Subtype.ext
  funext x y
  cases x with
  | inl x =>
      cases y with
      | inl y => exact jointConeZeroExtend_apply _ _ P x y
      | inr y =>
          change zeroExtendRaw
            (jointConeProdEmbedding (sumInlEmbedding X Z) (sumInlEmbedding Y W))
              (fun xy => P.1 xy.1 xy.2) (Sum.inl x, Sum.inr y) = 0
          simp [zeroExtendRaw, jointConeProdEmbedding, sumInlEmbedding]
  | inr x =>
      cases y with
      | inl y =>
          change zeroExtendRaw
            (jointConeProdEmbedding (sumInlEmbedding X Z) (sumInlEmbedding Y W))
              (fun xy => P.1 xy.1 xy.2) (Sum.inr x, Sum.inl y) = 0
          simp [zeroExtendRaw, jointConeProdEmbedding, sumInlEmbedding]
      | inr y =>
          change zeroExtendRaw
            (jointConeProdEmbedding (sumInlEmbedding X Z) (sumInlEmbedding Y W))
              (fun xy => P.1 xy.1 xy.2) (Sum.inr x, Sum.inr y) = 0
          simp [zeroExtendRaw, jointConeProdEmbedding, sumInlEmbedding]

/-- A zero matrix remains zero after any row and column embeddings. -/
theorem jointConeZeroExtend_eq_zero
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointCone X Y)
    (hP : ∀ x y, P x y = 0) :
    jointConeZeroExtend eX eY P =
      (⟨fun _ _ => 0, fun _ _ => le_rfl⟩ : JointCone X' Y') := by
  apply Subtype.ext
  funext x y
  change zeroExtendRaw (jointConeProdEmbedding eX eY)
      (fun xy => P.1 xy.1 xy.2) (x, y) = 0
  unfold zeroExtendRaw
  split <;> rename_i h
  · exact hP (Classical.choose h).1 (Classical.choose h).2
  · rfl

@[simp] theorem jointConeDirectSum_apply_inl_inl
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    (P : JointCone X Y) (Q : JointCone X' Y') (x : X) (y : Y) :
    jointConeDirectSum P Q (Sum.inl x) (Sum.inl y) = P x y := rfl

@[simp] theorem jointConeDirectSum_apply_inr_inr
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    (P : JointCone X Y) (Q : JointCone X' Y') (x : X') (y : Y') :
    jointConeDirectSum P Q (Sum.inr x) (Sum.inr y) = Q x y := rfl

@[simp] theorem jointConeDirectSum_apply_inl_inr
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    (P : JointCone X Y) (Q : JointCone X' Y') (x : X) (y : Y') :
    jointConeDirectSum P Q (Sum.inl x) (Sum.inr y) = 0 := rfl

@[simp] theorem jointConeDirectSum_apply_inr_inl
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    (P : JointCone X Y) (Q : JointCone X' Y') (x : X') (y : Y) :
    jointConeDirectSum P Q (Sum.inr x) (Sum.inl y) = 0 := rfl

@[simp] theorem jointConeTensor_apply
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    (P : JointCone X Y) (Q : JointCone X' Y')
    (x : X × X') (y : Y × Y') :
    jointConeTensor P Q x y = P x.1 y.1 * Q x.2 y.2 := rfl

@[simp] theorem jointConeRelabel_apply
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    (eX : X ≃ X') (eY : Y ≃ Y') (P : JointCone X Y) (x : X') (y : Y') :
    jointConeRelabel eX eY P x y = P (eX.symm x) (eY.symm y) := rfl

/-- Direct sum implements addition of total masses. -/
theorem jointConeMass_directSum
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (P : JointCone X Y) (Q : JointCone X' Y') :
    jointConeMass (jointConeDirectSum P Q) = jointConeMass P + jointConeMass Q := by
  simp [jointConeMass, jointConeDirectSum, add_comm]

/-- Tensor product implements multiplication of total masses. -/
theorem jointConeMass_tensor
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (P : JointCone X Y) (Q : JointCone X' Y') :
    jointConeMass (jointConeTensor P Q) = jointConeMass P * jointConeMass Q := by
  simp only [jointConeMass, jointConeTensor_apply, Fintype.sum_prod_type]
  calc
    (∑ x, ∑ x', ∑ y, ∑ y', P x y * Q x' y') =
        ∑ x, ∑ x', (∑ y, P x y) * (∑ y', Q x' y') := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro x' _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
    _ = ∑ x, (∑ y, P x y) * (∑ x', ∑ y', Q x' y') := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    _ = (∑ x, ∑ y, P x y) * (∑ x', ∑ y', Q x' y') := by
      rw [Finset.sum_mul]

@[simp] theorem jointConeMass_zero : jointConeMass jointConeZero = 0 := by
  simp [jointConeMass, jointConeZero]

@[simp] theorem jointConeMass_one : jointConeMass jointConeOne = 1 := by
  simp [jointConeMass, jointConeOne]

/-- Relabelling by finite equivalences preserves total mass. -/
theorem jointConeMass_relabel
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (eX : X ≃ X') (eY : Y ≃ Y') (P : JointCone X Y) :
    jointConeMass (jointConeRelabel eX eY P) = jointConeMass P := by
  simp only [jointConeMass, jointConeRelabel_apply]
  calc
    (∑ x', ∑ y', P (eX.symm x') (eY.symm y')) =
        ∑ x', ∑ y, P (eX.symm x') y := by
      apply Finset.sum_congr rfl
      intro x' _
      exact eY.symm.sum_comp (fun y => P (eX.symm x') y)
    _ = ∑ x, ∑ y, P x y :=
      eX.symm.sum_comp (fun x => ∑ y, P x y)

/-- Direct sum is commutative after the canonical relabelling of both finite
alphabets. -/
theorem jointConeDirectSum_comm_relabel
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    (P : JointCone X Y) (Q : JointCone X' Y') :
    jointConeRelabel (Equiv.sumComm X X') (Equiv.sumComm Y Y')
        (jointConeDirectSum P Q) =
      jointConeDirectSum Q P := by
  apply Subtype.ext
  funext x y
  cases x <;> cases y <;> rfl

/-- Direct sum is associative after the canonical relabelling. -/
theorem jointConeDirectSum_assoc_relabel
    {X₁ : Type u} {Y₁ : Type v} {X₂ : Type w} {Y₂ : Type z}
    {X₃ : Type*} {Y₃ : Type*}
    (P : JointCone X₁ Y₁) (Q : JointCone X₂ Y₂) (R : JointCone X₃ Y₃) :
    jointConeRelabel (Equiv.sumAssoc X₁ X₂ X₃) (Equiv.sumAssoc Y₁ Y₂ Y₃)
        (jointConeDirectSum (jointConeDirectSum P Q) R) =
      jointConeDirectSum P (jointConeDirectSum Q R) := by
  apply Subtype.ext
  funext x y
  rcases x with x₁ | (x₂ | x₃) <;>
    rcases y with y₁ | (y₂ | y₃) <;> rfl

/-- Tensor product is commutative after swapping both alphabets. -/
theorem jointConeTensor_comm_relabel
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    (P : JointCone X Y) (Q : JointCone X' Y') :
    jointConeRelabel (Equiv.prodComm X X') (Equiv.prodComm Y Y')
        (jointConeTensor P Q) =
      jointConeTensor Q P := by
  apply Subtype.ext
  funext x y
  simp [mul_comm]

/-- Tensor product is associative after the canonical relabelling. -/
theorem jointConeTensor_assoc_relabel
    {X₁ : Type u} {Y₁ : Type v} {X₂ : Type w} {Y₂ : Type z}
    {X₃ : Type*} {Y₃ : Type*}
    (P : JointCone X₁ Y₁) (Q : JointCone X₂ Y₂) (R : JointCone X₃ Y₃) :
    jointConeRelabel (Equiv.prodAssoc X₁ X₂ X₃) (Equiv.prodAssoc Y₁ Y₂ Y₃)
        (jointConeTensor (jointConeTensor P Q) R) =
      jointConeTensor P (jointConeTensor Q R) := by
  apply Subtype.ext
  funext x y
  simp [mul_assoc]

/-- Tensor product distributes over direct sum in the left argument after
the canonical type distributivity equivalences. -/
theorem jointConeTensor_directSum_left_relabel
    {X₁ : Type u} {Y₁ : Type v} {X₂ : Type w} {Y₂ : Type z}
    {X₃ : Type*} {Y₃ : Type*}
    (P : JointCone X₁ Y₁) (Q : JointCone X₂ Y₂) (R : JointCone X₃ Y₃) :
    jointConeRelabel (Equiv.sumProdDistrib X₁ X₂ X₃)
        (Equiv.sumProdDistrib Y₁ Y₂ Y₃)
        (jointConeTensor (jointConeDirectSum P Q) R) =
      jointConeDirectSum (jointConeTensor P R) (jointConeTensor Q R) := by
  apply Subtype.ext
  funext x y
  rcases x with ⟨x, r⟩ | ⟨x, r⟩ <;>
    rcases y with ⟨y, s⟩ | ⟨y, s⟩ <;>
    simp [jointConeRelabel, jointConeTensor, jointConeDirectSum]

/-- Tensor product distributes over direct sum in the right argument after
the canonical type distributivity equivalences. -/
theorem jointConeTensor_directSum_right_relabel
    {X₁ : Type u} {Y₁ : Type v} {X₂ : Type w} {Y₂ : Type z}
    {X₃ : Type*} {Y₃ : Type*}
    (P : JointCone X₁ Y₁) (Q : JointCone X₂ Y₂) (R : JointCone X₃ Y₃) :
    jointConeRelabel (Equiv.prodSumDistrib X₁ X₂ X₃)
        (Equiv.prodSumDistrib Y₁ Y₂ Y₃)
        (jointConeTensor P (jointConeDirectSum Q R)) =
      jointConeDirectSum (jointConeTensor P Q) (jointConeTensor P R) := by
  apply Subtype.ext
  funext x y
  rcases x with ⟨x, q⟩ | ⟨x, r⟩ <;>
    rcases y with ⟨y, q'⟩ | ⟨y, r'⟩ <;>
    simp [jointConeRelabel, jointConeTensor, jointConeDirectSum]

end ConditionalEntropy
