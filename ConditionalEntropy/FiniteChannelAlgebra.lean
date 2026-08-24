import ConditionalEntropy.FiniteChannels

/-!
# Algebra of finite conditional mixing channels

The manuscript uses closure of conditional mixing channels under sequential
composition, block direct sum, and tensor product.  The concrete `CMData`
format indexes a family by `Fin n`.  For algebraic constructions it is cleaner
to work temporarily with arbitrary nonempty finite index types and then
reindex canonically by `Fintype.equivFin`.
-/

open scoped BigOperators

namespace ConditionalEntropy

universe u v w k

/-- A conditional mixing family with an arbitrary finite index type. -/
structure CMFamily (K : Type k) (X : Type u) (Y : Type v) (Y' : Type w)
    [Fintype K] [Fintype X] [Fintype Y'] where
  S : K → X → X → ℝ
  hS : ∀ k, DoublyStochastic (S k)
  D : K → Y → Y' → ℝ
  hD : ∀ k, NonnegMatrix (D k)
  hnorm : ∀ y, ∑ k, ∑ y', D k y y' = 1

/-- Canonically enumerate a nonempty finite channel family. -/
noncomputable def CMFamily.toCMData
    {K : Type k} {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype K] [Nonempty K] [Fintype X] [Fintype Y']
    (C : CMFamily K X Y Y') : CMData X Y Y' where
  n := Fintype.card K
  n_pos := Fintype.card_pos
  S i := C.S ((Fintype.equivFin K).symm i)
  hS i := C.hS ((Fintype.equivFin K).symm i)
  D i := C.D ((Fintype.equivFin K).symm i)
  hD i := C.hD ((Fintype.equivFin K).symm i)
  hnorm y := by
    simpa only using
      ((Fintype.equivFin K).symm.sum_comp
        (fun k => ∑ y', C.D k y y')).trans (C.hnorm y)

/-- Raw cone action of an arbitrarily indexed family. -/
noncomputable def CMFamily.outputConeRaw
    {K : Type k} {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype K] [Fintype X] [Fintype Y] [Fintype Y']
    (C : CMFamily K X Y Y') (P : JointCone X Y) : X → Y' → ℝ :=
  fun x y' => ∑ k, ∑ y, ∑ z, C.S k x z * P z y * C.D k y y'

/-- Reindexing a family by `Fin (card K)` does not change its action. -/
theorem CMFamily.toCMData_outputConeRaw
    {K : Type k} {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype K] [Nonempty K] [Fintype X] [Fintype Y] [Fintype Y']
    (C : CMFamily K X Y Y') (P : JointCone X Y) :
    cmOutputConeRaw C.toCMData P = C.outputConeRaw P := by
  funext x y'
  exact (Fintype.equivFin K).symm.sum_comp
    (fun k => ∑ y, ∑ z, C.S k x z * P z y * C.D k y y')

/-- Bundled family action; its proof obligations are inherited from the
canonically reindexed `CMData`. -/
noncomputable def CMFamily.outputCone
    {K : Type k} {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype K] [Nonempty K] [Fintype X] [Fintype Y] [Fintype Y']
    (C : CMFamily K X Y Y') (P : JointCone X Y) : JointCone X Y' :=
  cmOutputCone C.toCMData P

theorem CMFamily.outputCone_eq
    {K : Type k} {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype K] [Nonempty K] [Fintype X] [Fintype Y] [Fintype Y']
    (C : CMFamily K X Y Y') (P : JointCone X Y) :
    (C.outputCone P).1 = C.outputConeRaw P :=
  C.toCMData_outputConeRaw P

/-- Sequential composition of arbitrarily indexed conditional channel
families.  The first family `C` is applied before `E`. -/
noncomputable def CMFamily.comp
    {K : Type k} {L : Type*} {X : Type u} {Y : Type v}
    {Y' : Type w} {Y'' : Type*}
    [Fintype K] [Fintype L] [Fintype X] [Fintype Y'] [Fintype Y'']
    (C : CMFamily K X Y Y') (E : CMFamily L X Y' Y'') :
    CMFamily (K × L) X Y Y'' where
  S kl x z := ∑ t, E.S kl.2 x t * C.S kl.1 t z
  hS kl := by
    rcases kl with ⟨i, j⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x z
      exact Finset.sum_nonneg fun t _ =>
        mul_nonneg ((E.hS j).1 x t) ((C.hS i).1 t z)
    · intro x
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, (C.hS i).2.1, mul_one]
      exact (E.hS j).2.1 x
    · intro z
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, (E.hS j).2.2, one_mul]
      exact (C.hS i).2.2 z
  D kl y y'' := ∑ y', C.D kl.1 y y' * E.D kl.2 y' y''
  hD kl y y'' := Finset.sum_nonneg fun y' _ =>
    mul_nonneg (C.hD kl.1 y y') (E.hD kl.2 y' y'')
  hnorm y := by
    let shuffle :
        K × (L × (Y'' × Y')) ≃ K × (Y' × (L × Y'')) :=
      { toFun := fun a => (a.1, (a.2.2.2, (a.2.1, a.2.2.1)))
        invFun := fun b => (b.1, (b.2.2.1, (b.2.2.2, b.2.1)))
        left_inv := by intro a; rfl
        right_inv := by intro b; rfl }
    calc
      (∑ kl : K × L, ∑ y'', ∑ y',
          C.D kl.1 y y' * E.D kl.2 y' y'') =
          ∑ a : K × (L × (Y'' × Y')),
            C.D a.1 y a.2.2.2 * E.D a.2.1 a.2.2.2 a.2.2.1 := by
        simp only [Fintype.sum_prod_type]
      _ = ∑ b : K × (Y' × (L × Y'')),
            C.D b.1 y b.2.1 * E.D b.2.2.1 b.2.1 b.2.2.2 := by
        apply Fintype.sum_equiv shuffle
        intro a
        rfl
      _ = ∑ i, ∑ y', C.D i y y' * (∑ j, ∑ y'', E.D j y' y'') := by
        simp only [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro y' hy'
        simp_rw [Finset.mul_sum]
      _ = ∑ i, ∑ y', C.D i y y' := by
        simp_rw [E.hnorm, mul_one]
      _ = 1 := C.hnorm y

/-- Sequential composition in the original `Fin n` representation. -/
noncomputable def CMData.comp
    {X : Type u} {Y : Type v} {Y' : Type w} {Y'' : Type*}
    [Fintype X] [Fintype Y'] [Fintype Y'']
    (C : CMData X Y Y') (E : CMData X Y' Y'') : CMData X Y Y'' := by
  letI : Nonempty (Fin C.n) := ⟨⟨0, C.n_pos⟩⟩
  letI : Nonempty (Fin E.n) := ⟨⟨0, E.n_pos⟩⟩
  exact (CMFamily.comp
    ({ S := C.S, hS := C.hS, D := C.D, hD := C.hD, hnorm := C.hnorm } :
      CMFamily (Fin C.n) X Y Y')
    ({ S := E.S, hS := E.hS, D := E.D, hD := E.hD, hnorm := E.hnorm } :
      CMFamily (Fin E.n) X Y' Y'')).toCMData

/-- Applying a composed family is the same as applying its two factors in
sequence. -/
theorem CMFamily.outputCone_comp
    {K : Type k} {L : Type*} {X : Type u} {Y : Type v}
    {Y' : Type w} {Y'' : Type*}
    [Fintype K] [Nonempty K] [Fintype L] [Nonempty L]
    [Fintype X] [Fintype Y] [Fintype Y'] [Fintype Y'']
    (C : CMFamily K X Y Y') (E : CMFamily L X Y' Y'')
    (P : JointCone X Y) :
    (C.comp E).outputCone P = E.outputCone (C.outputCone P) := by
  classical
  apply Subtype.ext
  funext x y''
  rw [CMFamily.outputCone_eq (C.comp E) P,
    CMFamily.outputCone_eq E (C.outputCone P)]
  simp only [CMFamily.outputConeRaw]
  rw [CMFamily.outputCone_eq C P]
  simp only [CMFamily.outputConeRaw]
  simp only [CMFamily.comp, Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  let shuffle :
      K × (L × (Y × (X × (Y' × X)))) ≃
        L × (Y' × (X × (K × (Y × X)))) :=
    { toFun := fun a =>
        (a.2.1, (a.2.2.2.2.1,
          (a.2.2.2.2.2, (a.1, (a.2.2.1, a.2.2.2.1)))))
      invFun := fun b =>
        (b.2.2.2.1, (b.1, (b.2.2.2.2.1,
          (b.2.2.2.2.2, (b.2.1, b.2.2.1)))))
      left_inv := by intro a; rfl
      right_inv := by intro b; rfl }
  have hsum :
      (∑ a : K × (L × (Y × (X × (Y' × X)))),
        E.S a.2.1 x a.2.2.2.2.2 *
          C.S a.1 a.2.2.2.2.2 a.2.2.2.1 * P a.2.2.2.1 a.2.2.1 *
          (C.D a.1 a.2.2.1 a.2.2.2.2.1 *
            E.D a.2.1 a.2.2.2.2.1 y'')) =
        ∑ b : L × (Y' × (X × (K × (Y × X)))),
          E.S b.1 x b.2.2.1 *
            (C.S b.2.2.2.1 b.2.2.1 b.2.2.2.2.2 *
              P b.2.2.2.2.2 b.2.2.2.2.1 *
              C.D b.2.2.2.1 b.2.2.2.2.1 b.2.1) *
            E.D b.1 b.2.1 y'' := by
    apply Fintype.sum_equiv shuffle
    intro a
    rcases a with ⟨i, j, y, z, y', t⟩
    change E.S j x t * C.S i t z * P z y *
        (C.D i y y' * E.D j y' y'') =
      E.S j x t * (C.S i t z * P z y * C.D i y y') * E.D j y' y''
    ring
  simpa only [Fintype.sum_prod_type] using hsum

/-- Regard the existing `Fin n` channel format as an arbitrary finite
family. -/
def CMData.toFamily
    {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y'] (C : CMData X Y Y') :
    CMFamily (Fin C.n) X Y Y' where
  S := C.S
  hS := C.hS
  D := C.D
  hD := C.hD
  hnorm := C.hnorm

theorem CMData.toFamily_outputCone
    {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y] [Fintype Y']
    (C : CMData X Y Y') (P : JointCone X Y) :
    letI : Nonempty (Fin C.n) := ⟨⟨0, C.n_pos⟩⟩
    C.toFamily.outputCone P = cmOutputCone C P := by
  letI : Nonempty (Fin C.n) := ⟨⟨0, C.n_pos⟩⟩
  apply Subtype.ext
  funext x y'
  rw [CMFamily.outputCone_eq]
  rfl

/-- Concrete sequential composition has the expected action. -/
theorem CMData.outputCone_comp
    {X : Type u} {Y : Type v} {Y' : Type w} {Y'' : Type*}
    [Fintype X] [Fintype Y] [Fintype Y'] [Fintype Y'']
    (C : CMData X Y Y') (E : CMData X Y' Y'') (P : JointCone X Y) :
    cmOutputCone (C.comp E) P = cmOutputCone E (cmOutputCone C P) := by
  letI : Nonempty (Fin C.n) := ⟨⟨0, C.n_pos⟩⟩
  letI : Nonempty (Fin E.n) := ⟨⟨0, E.n_pos⟩⟩
  change (C.toFamily.comp E.toFamily).outputCone P =
    cmOutputCone E (cmOutputCone C P)
  rw [CMFamily.outputCone_comp, CMData.toFamily_outputCone,
    CMData.toFamily_outputCone]

/-- The fixed-row unnormalised conditional relation is transitive. -/
theorem CMRelCone.trans
    {X : Type u} {Y : Type v} {Y' : Type w} {Y'' : Type*}
    [Fintype X] [Fintype Y] [Fintype Y'] [Fintype Y'']
    {P : JointCone X Y} {Q : JointCone X Y'} {R : JointCone X Y''}
    (hPQ : CMRelCone P Q) (hQR : CMRelCone Q R) : CMRelCone P R := by
  rcases hPQ with ⟨C, rfl⟩
  rcases hQR with ⟨E, rfl⟩
  exact ⟨C.comp E, (CMData.outputCone_comp C E P).symm⟩

/-- Identity matrix on a finite alphabet. -/
noncomputable def identityMatrix (X : Type u) : X → X → ℝ :=
  by
    classical
    exact fun x z => if x = z then 1 else 0

theorem identityMatrix_doublyStochastic (X : Type u) [Fintype X] :
    DoublyStochastic (identityMatrix X) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x z
    change 0 ≤ if x = z then 1 else 0
    split_ifs <;> norm_num
  · intro x
    simp [identityMatrix]
  · intro z
    simp [identityMatrix]

/-- Block diagonal sum of square matrices. -/
def matrixDirectSum
    {X : Type u} {Z : Type v} (A : X → X → ℝ) (B : Z → Z → ℝ) :
    Sum X Z → Sum X Z → ℝ
  | .inl x, .inl x' => A x x'
  | .inr z, .inr z' => B z z'
  | _, _ => 0

theorem matrixDirectSum_doublyStochastic
    {X : Type u} {Z : Type v} [Fintype X] [Fintype Z]
    {A : X → X → ℝ} {B : Z → Z → ℝ}
    (hA : DoublyStochastic A) (hB : DoublyStochastic B) :
    DoublyStochastic (matrixDirectSum A B) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x z
    cases x <;> cases z
    · exact hA.1 _ _
    · exact le_rfl
    · exact le_rfl
    · exact hB.1 _ _
  · intro x
    cases x <;>
      simp [matrixDirectSum, hA.2.1, hB.2.1]
  · intro z
    cases z <;>
      simp [matrixDirectSum, hA.2.2, hB.2.2]

/-- Block direct sum of conditional channel families. -/
noncomputable def CMFamily.directSum
    {K : Type k} {L : Type*}
    {X : Type u} {Y : Type v} {Y' : Type w}
    {Z : Type*} {W : Type*} {W' : Type*}
    [Fintype K] [Fintype L] [Fintype X] [Fintype Y']
    [Fintype Z] [Fintype W']
    (C : CMFamily K X Y Y') (E : CMFamily L Z W W') :
    CMFamily (Sum K L) (Sum X Z) (Sum Y W) (Sum Y' W') where
  S
    | .inl i => matrixDirectSum (C.S i) (identityMatrix Z)
    | .inr j => matrixDirectSum (identityMatrix X) (E.S j)
  hS
    | .inl i => matrixDirectSum_doublyStochastic
        (C.hS i) (identityMatrix_doublyStochastic Z)
    | .inr j => matrixDirectSum_doublyStochastic
        (identityMatrix_doublyStochastic X) (E.hS j)
  D
    | .inl i, .inl y, .inl y' => C.D i y y'
    | .inr j, .inr w, .inr w' => E.D j w w'
    | _, _, _ => 0
  hD := by
    intro i y y'
    cases i <;> cases y <;> cases y'
    · exact C.hD _ _ _
    all_goals try exact E.hD _ _ _
    all_goals exact le_rfl
  hnorm := by
    intro y
    cases y with
    | inl y =>
        simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
          Finset.sum_const_zero, add_zero] using C.hnorm y
    | inr w =>
        simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
          Finset.sum_const_zero, zero_add] using E.hnorm w

/-- The block-sum channel acts blockwise on a block-sum input. -/
theorem CMFamily.outputCone_directSum
    {K : Type k} {L : Type*}
    {X : Type u} {Y : Type v} {Y' : Type w}
    {Z : Type*} {W : Type*} {W' : Type*}
    [Fintype K] [Nonempty K] [Fintype L] [Nonempty L]
    [Fintype X] [Fintype Y] [Fintype Y']
    [Fintype Z] [Fintype W] [Fintype W']
    (C : CMFamily K X Y Y') (E : CMFamily L Z W W')
    (P : JointCone X Y) (R : JointCone Z W) :
    (C.directSum E).outputCone (jointConeDirectSum P R) =
      jointConeDirectSum (C.outputCone P) (E.outputCone R) := by
  classical
  apply Subtype.ext
  funext x y'
  rw [CMFamily.outputCone_eq]
  cases x with
  | inl x =>
      cases y' with
      | inl y' =>
          rw [jointConeDirectSum_apply_inl_inl, CMFamily.outputCone_eq C P]
          simp [CMFamily.outputConeRaw, CMFamily.directSum, matrixDirectSum,
            identityMatrix, Fintype.sum_sum_type]
      | inr w' =>
          simp [CMFamily.outputConeRaw, CMFamily.directSum, matrixDirectSum,
            Fintype.sum_sum_type]
  | inr z =>
      cases y' with
      | inl y' =>
          simp [CMFamily.outputConeRaw, CMFamily.directSum, matrixDirectSum,
            Fintype.sum_sum_type]
      | inr w' =>
          rw [jointConeDirectSum_apply_inr_inr, CMFamily.outputCone_eq E R]
          simp [CMFamily.outputConeRaw, CMFamily.directSum, matrixDirectSum,
            identityMatrix, Fintype.sum_sum_type]

/-- Block direct sum in the original `Fin n` representation. -/
noncomputable def CMData.directSum
    {X : Type u} {Y : Type v} {Y' : Type w}
    {Z : Type*} {W : Type*} {W' : Type*}
    [Fintype X] [Fintype Y'] [Fintype Z] [Fintype W']
    (C : CMData X Y Y') (E : CMData Z W W') :
    CMData (Sum X Z) (Sum Y W) (Sum Y' W') := by
  letI : Nonempty (Fin C.n) := ⟨⟨0, C.n_pos⟩⟩
  letI : Nonempty (Fin E.n) := ⟨⟨0, E.n_pos⟩⟩
  exact (C.toFamily.directSum E.toFamily).toCMData

theorem CMData.outputCone_directSum
    {X : Type u} {Y : Type v} {Y' : Type w}
    {Z : Type*} {W : Type*} {W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Y']
    [Fintype Z] [Fintype W] [Fintype W']
    (C : CMData X Y Y') (E : CMData Z W W')
    (P : JointCone X Y) (R : JointCone Z W) :
    cmOutputCone (C.directSum E) (jointConeDirectSum P R) =
      jointConeDirectSum (cmOutputCone C P) (cmOutputCone E R) := by
  letI : Nonempty (Fin C.n) := ⟨⟨0, C.n_pos⟩⟩
  letI : Nonempty (Fin E.n) := ⟨⟨0, E.n_pos⟩⟩
  change (C.toFamily.directSum E.toFamily).outputCone
      (jointConeDirectSum P R) = _
  rw [CMFamily.outputCone_directSum, CMData.toFamily_outputCone,
    CMData.toFamily_outputCone]

/-- Concrete conditional majorization is closed under block direct sum. -/
theorem CMRelCone.directSum
    {X : Type u} {Y : Type v} {Y' : Type w}
    {Z : Type*} {W : Type*} {W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Y']
    [Fintype Z] [Fintype W] [Fintype W']
    {P : JointCone X Y} {Q : JointCone X Y'}
    {R : JointCone Z W} {T : JointCone Z W'}
    (hPQ : CMRelCone P Q) (hRT : CMRelCone R T) :
    CMRelCone (jointConeDirectSum P R) (jointConeDirectSum Q T) := by
  rcases hPQ with ⟨C, rfl⟩
  rcases hRT with ⟨E, rfl⟩
  exact ⟨C.directSum E, (CMData.outputCone_directSum C E P R).symm⟩

/-- Tensor product of conditional channel families. -/
noncomputable def CMFamily.tensor
    {K : Type k} {L : Type*}
    {X : Type u} {Y : Type v} {Y' : Type w}
    {Z : Type*} {W : Type*} {W' : Type*}
    [Fintype K] [Fintype L] [Fintype X] [Fintype Y']
    [Fintype Z] [Fintype W']
    (C : CMFamily K X Y Y') (E : CMFamily L Z W W') :
    CMFamily (K × L) (X × Z) (Y × W) (Y' × W') where
  S kl xz xz' := C.S kl.1 xz.1 xz'.1 * E.S kl.2 xz.2 xz'.2
  hS kl := by
    rcases kl with ⟨i, j⟩
    refine ⟨?_, ?_, ?_⟩
    · intro xz xz'
      exact mul_nonneg ((C.hS i).1 _ _) ((E.hS j).1 _ _)
    · intro xz
      simp only [Fintype.sum_prod_type]
      calc
        (∑ x', ∑ z', C.S i xz.1 x' * E.S j xz.2 z') =
            (∑ x', C.S i xz.1 x') * (∑ z', E.S j xz.2 z') := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x' hx'
          rw [Finset.mul_sum]
        _ = 1 := by rw [(C.hS i).2.1, (E.hS j).2.1, one_mul]
    · intro xz'
      simp only [Fintype.sum_prod_type]
      calc
        (∑ x, ∑ z, C.S i x xz'.1 * E.S j z xz'.2) =
            (∑ x, C.S i x xz'.1) * (∑ z, E.S j z xz'.2) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mul_sum]
        _ = 1 := by rw [(C.hS i).2.2, (E.hS j).2.2, one_mul]
  D kl yw yw' := C.D kl.1 yw.1 yw'.1 * E.D kl.2 yw.2 yw'.2
  hD kl yw yw' := mul_nonneg (C.hD kl.1 _ _) (E.hD kl.2 _ _)
  hnorm yw := by
    let shuffle :
        K × (L × (Y' × W')) ≃ K × (Y' × (L × W')) :=
      { toFun := fun a => (a.1, (a.2.2.1, (a.2.1, a.2.2.2)))
        invFun := fun b => (b.1, (b.2.2.1, (b.2.1, b.2.2.2)))
        left_inv := by intro a; rfl
        right_inv := by intro b; rfl }
    calc
      (∑ kl : K × L, ∑ yw' : Y' × W',
          C.D kl.1 yw.1 yw'.1 * E.D kl.2 yw.2 yw'.2) =
          ∑ a : K × (L × (Y' × W')),
            C.D a.1 yw.1 a.2.2.1 * E.D a.2.1 yw.2 a.2.2.2 := by
        simp only [Fintype.sum_prod_type]
      _ = ∑ b : K × (Y' × (L × W')),
            C.D b.1 yw.1 b.2.1 * E.D b.2.2.1 yw.2 b.2.2.2 := by
        apply Fintype.sum_equiv shuffle
        intro a
        rfl
      _ = ∑ i, ∑ y', C.D i yw.1 y' *
            (∑ j, ∑ w', E.D j yw.2 w') := by
        simp only [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro y' hy'
        simp_rw [Finset.mul_sum]
      _ = ∑ i, ∑ y', C.D i yw.1 y' := by
        simp_rw [E.hnorm, mul_one]
      _ = 1 := C.hnorm yw.1

/-- The tensor channel acts as the tensor product of the two component
actions. -/
theorem CMFamily.outputCone_tensor
    {K : Type k} {L : Type*}
    {X : Type u} {Y : Type v} {Y' : Type w}
    {Z : Type*} {W : Type*} {W' : Type*}
    [Fintype K] [Nonempty K] [Fintype L] [Nonempty L]
    [Fintype X] [Fintype Y] [Fintype Y']
    [Fintype Z] [Fintype W] [Fintype W']
    (C : CMFamily K X Y Y') (E : CMFamily L Z W W')
    (P : JointCone X Y) (R : JointCone Z W) :
    (C.tensor E).outputCone (jointConeTensor P R) =
      jointConeTensor (C.outputCone P) (E.outputCone R) := by
  classical
  apply Subtype.ext
  funext xz yw'
  rw [CMFamily.outputCone_eq, jointConeTensor_apply,
    CMFamily.outputCone_eq C P, CMFamily.outputCone_eq E R]
  simp only [CMFamily.outputConeRaw, CMFamily.tensor,
    jointConeTensor_apply, Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  let shuffle :
      K × (L × (Y × (W × (X × Z)))) ≃
        L × (W × (Z × (K × (Y × X)))) :=
    { toFun := fun a =>
        (a.2.1, (a.2.2.2.1, (a.2.2.2.2.2,
          (a.1, (a.2.2.1, a.2.2.2.2.1)))))
      invFun := fun b =>
        (b.2.2.2.1, (b.1, (b.2.2.2.2.1,
          (b.2.1, (b.2.2.2.2.2, b.2.2.1)))))
      left_inv := by intro a; rfl
      right_inv := by intro b; rfl }
  have hsum :
      (∑ a : K × (L × (Y × (W × (X × Z)))),
        C.S a.1 xz.1 a.2.2.2.2.1 * E.S a.2.1 xz.2 a.2.2.2.2.2 *
          (P a.2.2.2.2.1 a.2.2.1 * R a.2.2.2.2.2 a.2.2.2.1) *
          (C.D a.1 a.2.2.1 yw'.1 * E.D a.2.1 a.2.2.2.1 yw'.2)) =
        ∑ b : L × (W × (Z × (K × (Y × X)))),
          (C.S b.2.2.2.1 xz.1 b.2.2.2.2.2 *
            P b.2.2.2.2.2 b.2.2.2.2.1 *
            C.D b.2.2.2.1 b.2.2.2.2.1 yw'.1) *
          (E.S b.1 xz.2 b.2.2.1 * R b.2.2.1 b.2.1 *
            E.D b.1 b.2.1 yw'.2) := by
    apply Fintype.sum_equiv shuffle
    intro a
    rcases a with ⟨i, j, y, w, x', z'⟩
    change C.S i xz.1 x' * E.S j xz.2 z' * (P x' y * R z' w) *
        (C.D i y yw'.1 * E.D j w yw'.2) =
      (C.S i xz.1 x' * P x' y * C.D i y yw'.1) *
        (E.S j xz.2 z' * R z' w * E.D j w yw'.2)
    ring
  simpa only [Fintype.sum_prod_type] using hsum

/-- Tensor product in the original `Fin n` representation. -/
noncomputable def CMData.tensor
    {X : Type u} {Y : Type v} {Y' : Type w}
    {Z : Type*} {W : Type*} {W' : Type*}
    [Fintype X] [Fintype Y'] [Fintype Z] [Fintype W']
    (C : CMData X Y Y') (E : CMData Z W W') :
    CMData (X × Z) (Y × W) (Y' × W') := by
  letI : Nonempty (Fin C.n) := ⟨⟨0, C.n_pos⟩⟩
  letI : Nonempty (Fin E.n) := ⟨⟨0, E.n_pos⟩⟩
  exact (C.toFamily.tensor E.toFamily).toCMData

theorem CMData.outputCone_tensor
    {X : Type u} {Y : Type v} {Y' : Type w}
    {Z : Type*} {W : Type*} {W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Y']
    [Fintype Z] [Fintype W] [Fintype W']
    (C : CMData X Y Y') (E : CMData Z W W')
    (P : JointCone X Y) (R : JointCone Z W) :
    cmOutputCone (C.tensor E) (jointConeTensor P R) =
      jointConeTensor (cmOutputCone C P) (cmOutputCone E R) := by
  letI : Nonempty (Fin C.n) := ⟨⟨0, C.n_pos⟩⟩
  letI : Nonempty (Fin E.n) := ⟨⟨0, E.n_pos⟩⟩
  change (C.toFamily.tensor E.toFamily).outputCone (jointConeTensor P R) = _
  rw [CMFamily.outputCone_tensor, CMData.toFamily_outputCone,
    CMData.toFamily_outputCone]

/-- Concrete conditional majorization is closed under tensor product. -/
theorem CMRelCone.tensor
    {X : Type u} {Y : Type v} {Y' : Type w}
    {Z : Type*} {W : Type*} {W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Y']
    [Fintype Z] [Fintype W] [Fintype W']
    {P : JointCone X Y} {Q : JointCone X Y'}
    {R : JointCone Z W} {T : JointCone Z W'}
    (hPQ : CMRelCone P Q) (hRT : CMRelCone R T) :
    CMRelCone (jointConeTensor P R) (jointConeTensor Q T) := by
  rcases hPQ with ⟨C, rfl⟩
  rcases hRT with ⟨E, rfl⟩
  exact ⟨C.tensor E, (CMData.outputCone_tensor C E P R).symm⟩

/-- Sequential composition also has the expected action on normalized joint
probabilities. -/
theorem CMData.output_comp
    {X : Type u} {Y : Type v} {Y' : Type w} {Y'' : Type*}
    [Fintype X] [Fintype Y] [Fintype Y'] [Fintype Y'']
    (C : CMData X Y Y') (E : CMData X Y' Y'') (P : JointProb X Y) :
    cmOutput (C.comp E) P = cmOutput E (cmOutput C P) := by
  apply Subtype.ext
  have hcone :
      jointProbToCone (cmOutput (C.comp E) P) =
        jointProbToCone (cmOutput E (cmOutput C P)) := by
    calc
      jointProbToCone (cmOutput (C.comp E) P) =
          cmOutputCone (C.comp E) (jointProbToCone P) :=
        (cmOutputCone_jointProb (C.comp E) P).symm
      _ = cmOutputCone E (cmOutputCone C (jointProbToCone P)) :=
        CMData.outputCone_comp C E (jointProbToCone P)
      _ = jointProbToCone (cmOutput E (cmOutput C P)) := by
        rw [cmOutputCone_jointProb C P,
          cmOutputCone_jointProb E (cmOutput C P)]
  exact congrArg (fun R : JointCone X Y'' => R.1) hcone

/-- The normalized fixed-row relation is transitive. -/
theorem CMRel.trans
    {X : Type u} {Y : Type v} {Y' : Type w} {Y'' : Type*}
    [Fintype X] [Fintype Y] [Fintype Y'] [Fintype Y'']
    {P : JointProb X Y} {Q : JointProb X Y'} {R : JointProb X Y''}
    (hPQ : CMRel P Q) (hQR : CMRel Q R) : CMRel P R := by
  rw [cmRel_iff_eq_output] at hPQ hQR ⊢
  rcases hPQ with ⟨C, rfl⟩
  rcases hQR with ⟨E, rfl⟩
  exact ⟨C.comp E, (CMData.output_comp C E P).symm⟩

/-- A heterogeneous column alphabet over a fixed row alphabet. -/
structure FixedRowCone (X : Type u) [Fintype X] where
  Y : Type v
  fintypeY : Fintype Y
  matrix : JointCone X Y

attribute [instance] FixedRowCone.fintypeY

/-- Concrete channel comparison on the fixed-row sigma type. -/
def FixedRowCone.CMRel
    {X : Type u} [Fintype X] (P Q : FixedRowCone.{u, v} X) : Prop :=
  CMRelCone P.matrix Q.matrix

theorem FixedRowCone.CMRel.refl
    {X : Type u} [Fintype X] (P : FixedRowCone.{u, v} X) : P.CMRel P :=
  CMRelCone.refl P.matrix

theorem FixedRowCone.CMRel.trans
    {X : Type u} [Fintype X] {P Q R : FixedRowCone.{u, v} X}
    (hPQ : P.CMRel Q) (hQR : Q.CMRel R) : P.CMRel R :=
  CMRelCone.trans hPQ hQR

/-- Every finite aligned chain of manuscript channels compresses to one
explicit `CMData`, and conversely one channel is a one-step chain. -/
theorem FixedRowCone.reflTransGen_cmRel_iff
    {X : Type u} [Fintype X] (P Q : FixedRowCone.{u, v} X) :
    Relation.ReflTransGen FixedRowCone.CMRel P Q ↔ P.CMRel Q := by
  constructor
  · intro h
    induction h with
    | refl => exact FixedRowCone.CMRel.refl P
    | tail h hstep ih => exact ih.trans hstep
  · intro h
    exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl h

end ConditionalEntropy
