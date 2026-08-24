import ConditionalEntropy.FiniteData
import ConditionalEntropy.FiniteSemiring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite stochastic matrices, conditional channels, and embedding lift

This file gives a proof-carrying version of the manuscript's original finite
channel model.  A conditional mixing channel is a finite family of doubly
stochastic row maps and nonnegative selection matrices whose aggregate is row
stochastic.  Its output is proved entrywise nonnegative and mass preserving.

The final part defines the polymorphic joint functional used by the paper and
proves the zero-embedding lift from fixed-row conditional-channel monotonicity
to conditional majorization between different finite alphabets.
-/

open scoped BigOperators

namespace ConditionalEntropy

universe u v w z

/-- Coordinatewise nonnegativity of a real matrix. -/
def NonnegMatrix {I : Type u} {J : Type v} (D : I → J → ℝ) : Prop :=
  ∀ i j, 0 ≤ D i j

/-- A raw matrix is row stochastic.  This predicate is named differently from
the older bundled `RowStochastic` structure in `Conditioning.lean`. -/
def IsRowStochastic {I : Type u} {J : Type v} [Fintype J]
    (D : I → J → ℝ) : Prop :=
  NonnegMatrix D ∧ ∀ i, ∑ j, D i j = 1

/-- A raw matrix is row sub-stochastic. -/
def SubStochastic {I : Type u} {J : Type v} [Fintype J]
    (D : I → J → ℝ) : Prop :=
  NonnegMatrix D ∧ ∀ i, ∑ j, D i j ≤ 1

/-- A square matrix is doubly stochastic. -/
def DoublyStochastic {I : Type u} [Fintype I] (S : I → I → ℝ) : Prop :=
  NonnegMatrix S ∧
    (∀ i, ∑ j, S i j = 1) ∧
    ∀ j, ∑ i, S i j = 1

/-- Left action of a finite raw matrix on a vector. -/
noncomputable def matrixAction {I : Type u} {J : Type v} [Fintype J]
    (S : I → J → ℝ) (x : J → ℝ) (i : I) : ℝ :=
  ∑ j, S i j * x j

/-- A nonnegative matrix maps a cone vector to a cone vector. -/
noncomputable def coneMatrixAction {I : Type u} {J : Type v}
    [Fintype J] (S : I → J → ℝ) (hS : NonnegMatrix S)
    (x : ConeVec J) : ConeVec I :=
  ⟨matrixAction S x.1,
   fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hS i j) (x.2 j)⟩

@[simp] theorem coneMatrixAction_apply {I : Type u} {J : Type v}
    [Fintype J] (S : I → J → ℝ) (hS : NonnegMatrix S)
    (x : ConeVec J) (i : I) :
    (coneMatrixAction S hS x).1 i = ∑ j, S i j * x.1 j := rfl

/-- A doubly stochastic action preserves the mass of every nonnegative
vector. -/
theorem doublyStochastic_mass {I : Type u} [Fintype I]
    (S : I → I → ℝ) (hS : DoublyStochastic S) (x : ConeVec I) :
    l1Mass (coneMatrixAction S hS.1 x).1 = l1Mass x.1 := by
  change NonnegMatrix S ∧
    (∀ i, ∑ j, S i j = 1) ∧ ∀ j, ∑ i, S i j = 1 at hS
  simp only [l1Mass, coneMatrixAction, matrixAction]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hS.2.2, one_mul]

/-- A doubly stochastic matrix maps probability vectors to probability
vectors. -/
noncomputable def probMatrixAction {I : Type u} [Fintype I]
    (S : I → I → ℝ) (hS : DoublyStochastic S)
    (p : ProbVec I) : ProbVec I :=
  ⟨matrixAction S p.1,
   ⟨fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hS.1 i j) (p.2.1 j), by
     change l1Mass (coneMatrixAction S hS.1 ⟨p.1, p.2.1⟩).1 = 1
     exact (doublyStochastic_mass S hS ⟨p.1, p.2.1⟩).trans p.2.2⟩⟩

/-- Finite data for a conditionally mixing channel from `X × Y` to
`X × Y'`.  The stored aggregate normalization is equivalent to requiring
each selection matrix to be sub-stochastic and their sum row stochastic. -/
structure CMData (X : Type u) (Y : Type v) (Y' : Type w)
    [Fintype X] [Fintype Y'] where
  n : ℕ
  n_pos : 0 < n
  S : Fin n → X → X → ℝ
  hS : ∀ k, DoublyStochastic (S k)
  D : Fin n → Y → Y' → ℝ
  hD : ∀ k, NonnegMatrix (D k)
  hnorm : ∀ y, ∑ k, ∑ y', D k y y' = 1

/-- Identity conditional channel. -/
noncomputable def CMData.identity (X : Type u) (Y : Type v)
    [Fintype X] [Fintype Y] : CMData X Y Y := by
  classical
  exact
    { n := 1
      n_pos := by norm_num
      S := fun _ x z => if x = z then 1 else 0
      hS := by
        intro k
        refine ⟨?_, ?_, ?_⟩
        · intro x z
          change 0 ≤ if x = z then 1 else 0
          split_ifs <;> norm_num
        · intro x
          simp
        · intro z
          simp
      D := fun _ y y' => if y = y' then 1 else 0
      hD := by
        intro k y y'
        change 0 ≤ if y = y' then 1 else 0
        split_ifs <;> norm_num
      hnorm := by
        intro y
        simp }

/-- Sum of the selection matrices in a conditional channel. -/
noncomputable def cmSelectionSum {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y'] (C : CMData X Y Y') : Y → Y' → ℝ :=
  fun y y' => ∑ k, C.D k y y'

/-- The aggregate selection matrix of a conditional channel is row
stochastic. -/
theorem cmSelectionSum_rowStochastic {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y'] (C : CMData X Y Y') :
    IsRowStochastic (cmSelectionSum C) := by
  constructor
  · intro y y'
    exact Finset.sum_nonneg fun k _ => C.hD k y y'
  · intro y
    simp only [cmSelectionSum]
    rw [Finset.sum_comm]
    exact C.hnorm y

/-- Every individual selection matrix in a conditional channel is
sub-stochastic. -/
theorem cmSelection_subStochastic {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y'] (C : CMData X Y Y') (k : Fin C.n) :
    SubStochastic (C.D k) := by
  refine ⟨C.hD k, ?_⟩
  intro y
  calc
    ∑ y', C.D k y y' ≤ ∑ j, ∑ y', C.D j y y' := by
      exact Finset.single_le_sum
        (fun j _ => Finset.sum_nonneg fun y' _ => C.hD j y y')
        (Finset.mem_univ k)
    _ = 1 := C.hnorm y

/-- The raw output of a conditional mixing channel. -/
noncomputable def cmOutputRaw {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y] [Fintype Y']
    (C : CMData X Y Y') (P : JointProb X Y) : X → Y' → ℝ :=
  fun x y' => ∑ k, ∑ y, ∑ z, C.S k x z * P.1 z y * C.D k y y'

/-- The raw conditional-channel output is entrywise nonnegative and has total
mass one. -/
theorem fndCmOutputRaw {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y] [Fintype Y']
    (C : CMData X Y Y') (P : JointProb X Y) :
    (∀ x y', 0 ≤ cmOutputRaw C P x y') ∧
      (∑ x, ∑ y', cmOutputRaw C P x y') = 1 := by
  classical
  constructor
  · intro x y'
    exact Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun y _ =>
        Finset.sum_nonneg fun z _ => by
          have hk : NonnegMatrix (C.S k) ∧
              (∀ i, ∑ j, C.S k i j = 1) ∧
              ∀ j, ∑ i, C.S k i j = 1 := C.hS k
          exact mul_nonneg (mul_nonneg (hk.1 x z) (P.2.1 z y)) (C.hD k y y')
  · let shuffle :
        X × (Y' × (Fin C.n × (Y × X))) ≃
          X × (Y × (Fin C.n × (Y' × X))) :=
      { toFun := fun a =>
          (a.2.2.2.2, (a.2.2.2.1, (a.2.2.1, (a.2.1, a.1))))
        invFun := fun b =>
          (b.2.2.2.2, (b.2.2.2.1, (b.2.2.1, (b.2.1, b.1))))
        left_inv := by intro a; rfl
        right_inv := by intro b; rfl }
    calc
      (∑ x, ∑ y', cmOutputRaw C P x y') =
          ∑ a : X × (Y' × (Fin C.n × (Y × X))),
            C.S a.2.2.1 a.1 a.2.2.2.2 * P.1 a.2.2.2.2 a.2.2.2.1 *
              C.D a.2.2.1 a.2.2.2.1 a.2.1 := by
        simp only [cmOutputRaw, Fintype.sum_prod_type]
      _ = ∑ b : X × (Y × (Fin C.n × (Y' × X))),
            P.1 b.1 b.2.1 * C.D b.2.2.1 b.2.1 b.2.2.2.1 *
              C.S b.2.2.1 b.2.2.2.2 b.1 := by
        apply Fintype.sum_equiv shuffle
        intro a
        rcases a with ⟨x, ⟨y', ⟨k, ⟨y, z⟩⟩⟩⟩
        change C.S k x z * P.1 z y * C.D k y y' =
          P.1 z y * C.D k y y' * C.S k x z
        ring
      _ = ∑ z, ∑ y, ∑ k, ∑ y', ∑ x,
            P.1 z y * C.D k y y' * C.S k x z := by
        simp only [Fintype.sum_prod_type]
      _ = ∑ z, ∑ y, ∑ k, ∑ y', P.1 z y * C.D k y y' := by
        apply Finset.sum_congr rfl
        intro z _
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro y' _
        have hk : NonnegMatrix (C.S k) ∧
            (∀ i, ∑ j, C.S k i j = 1) ∧
            ∀ j, ∑ i, C.S k i j = 1 := C.hS k
        rw [← Finset.mul_sum, hk.2.2 z, mul_one]
      _ = ∑ z, ∑ y, P.1 z y * (∑ k, ∑ y', C.D k y y') := by
        apply Finset.sum_congr rfl
        intro z _
        apply Finset.sum_congr rfl
        intro y _
        simp_rw [Finset.mul_sum]
      _ = ∑ z, ∑ y, P.1 z y := by
        simp_rw [C.hnorm, mul_one]
      _ = 1 := P.2.2

/-- The bundled probability output of a conditional mixing channel. -/
noncomputable def cmOutput {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y] [Fintype Y']
    (C : CMData X Y Y') (P : JointProb X Y) : JointProb X Y' :=
  ⟨cmOutputRaw C P, fndCmOutputRaw C P⟩

/-- Forget normalization and view a joint probability matrix as an
unnormalized semiring representative. -/
def jointProbToCone {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (P : JointProb X Y) : JointCone X Y :=
  ⟨P.1, P.2.1⟩

@[simp] theorem jointProbToCone_mass {X : Type u} {Y : Type v}
    [Fintype X] [Fintype Y] (P : JointProb X Y) :
    jointConeMass (jointProbToCone P) = 1 := P.2.2

/-- The manuscript's conditional-channel formula on an arbitrary
unnormalized nonnegative matrix. -/
noncomputable def cmOutputConeRaw {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y] [Fintype Y']
    (C : CMData X Y Y') (P : JointCone X Y) : X → Y' → ℝ :=
  fun x y' => ∑ k, ∑ y, ∑ z, C.S k x z * P.1 z y * C.D k y y'

theorem cmOutputConeRaw_nonneg {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y] [Fintype Y']
    (C : CMData X Y Y') (P : JointCone X Y) :
    ∀ x y', 0 ≤ cmOutputConeRaw C P x y' := by
  intro x y'
  exact Finset.sum_nonneg fun k _ =>
    Finset.sum_nonneg fun y _ =>
      Finset.sum_nonneg fun z _ => by
        have hk : NonnegMatrix (C.S k) ∧
            (∀ i, ∑ j, C.S k i j = 1) ∧
            ∀ j, ∑ i, C.S k i j = 1 := C.hS k
        exact mul_nonneg (mul_nonneg (hk.1 x z) (P.2 z y)) (C.hD k y y')

/-- Conditional mixing preserves the total mass of every unnormalized
nonnegative matrix. -/
theorem cmOutputConeRaw_mass {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y] [Fintype Y']
    (C : CMData X Y Y') (P : JointCone X Y) :
    (∑ x, ∑ y', cmOutputConeRaw C P x y') = jointConeMass P := by
  classical
  let shuffle :
      X × (Y' × (Fin C.n × (Y × X))) ≃
        X × (Y × (Fin C.n × (Y' × X))) :=
    { toFun := fun a =>
        (a.2.2.2.2, (a.2.2.2.1, (a.2.2.1, (a.2.1, a.1))))
      invFun := fun b =>
        (b.2.2.2.2, (b.2.2.2.1, (b.2.2.1, (b.2.1, b.1))))
      left_inv := by intro a; rfl
      right_inv := by intro b; rfl }
  calc
    (∑ x, ∑ y', cmOutputConeRaw C P x y') =
        ∑ a : X × (Y' × (Fin C.n × (Y × X))),
          C.S a.2.2.1 a.1 a.2.2.2.2 * P.1 a.2.2.2.2 a.2.2.2.1 *
            C.D a.2.2.1 a.2.2.2.1 a.2.1 := by
      simp only [cmOutputConeRaw, Fintype.sum_prod_type]
    _ = ∑ b : X × (Y × (Fin C.n × (Y' × X))),
          P.1 b.1 b.2.1 * C.D b.2.2.1 b.2.1 b.2.2.2.1 *
            C.S b.2.2.1 b.2.2.2.2 b.1 := by
      apply Fintype.sum_equiv shuffle
      intro a
      rcases a with ⟨x, ⟨y', ⟨k, ⟨y, z⟩⟩⟩⟩
      change C.S k x z * P.1 z y * C.D k y y' =
        P.1 z y * C.D k y y' * C.S k x z
      ring
    _ = ∑ z, ∑ y, ∑ k, ∑ y', ∑ x,
          P.1 z y * C.D k y y' * C.S k x z := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ z, ∑ y, ∑ k, ∑ y', P.1 z y * C.D k y y' := by
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro y' _
      have hk : NonnegMatrix (C.S k) ∧
          (∀ i, ∑ j, C.S k i j = 1) ∧
          ∀ j, ∑ i, C.S k i j = 1 := C.hS k
      rw [← Finset.mul_sum, hk.2.2 z, mul_one]
    _ = ∑ z, ∑ y, P.1 z y * (∑ k, ∑ y', C.D k y y') := by
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro y _
      simp_rw [Finset.mul_sum]
    _ = ∑ z, ∑ y, P.1 z y := by
      simp_rw [C.hnorm, mul_one]
    _ = jointConeMass P := rfl

/-- Bundled unnormalized output. -/
noncomputable def cmOutputCone {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y] [Fintype Y']
    (C : CMData X Y Y') (P : JointCone X Y) : JointCone X Y' :=
  ⟨cmOutputConeRaw C P, cmOutputConeRaw_nonneg C P⟩

@[simp] theorem cmOutputCone_identity {X : Type u} {Y : Type v}
    [Fintype X] [Fintype Y] (P : JointCone X Y) :
    cmOutputCone (CMData.identity X Y) P = P := by
  classical
  apply Subtype.ext
  funext x y
  simp [cmOutputCone, cmOutputConeRaw, CMData.identity]

@[simp] theorem cmOutputCone_mass {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y] [Fintype Y']
    (C : CMData X Y Y') (P : JointCone X Y) :
    jointConeMass (cmOutputCone C P) = jointConeMass P :=
  cmOutputConeRaw_mass C P

/-- The normalized and unnormalized channel actions are the same underlying
matrix. -/
theorem cmOutputCone_jointProb {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y] [Fintype Y']
    (C : CMData X Y Y') (P : JointProb X Y) :
    cmOutputCone C (jointProbToCone P) = jointProbToCone (cmOutput C P) := by
  rfl

/-- Conditional mixing relation on unnormalized semiring representatives. -/
def CMRelCone {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y] [Fintype Y']
    (P : JointCone X Y) (Q : JointCone X Y') : Prop :=
  ∃ C : CMData X Y Y', Q = cmOutputCone C P

theorem CMRelCone.refl {X : Type u} {Y : Type v}
    [Fintype X] [Fintype Y] (P : JointCone X Y) : CMRelCone P P :=
  ⟨CMData.identity X Y, (cmOutputCone_identity P).symm⟩

theorem CMRelCone.mass_eq {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y] [Fintype Y']
    {P : JointCone X Y} {Q : JointCone X Y'} (h : CMRelCone P Q) :
    jointConeMass Q = jointConeMass P := by
  rcases h with ⟨C, rfl⟩
  exact cmOutputCone_mass C P

/-- Fixed-row conditional mixing relation. -/
def CMRel {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y] [Fintype Y']
    (P : JointProb X Y) (Q : JointProb X Y') : Prop :=
  ∃ C : CMData X Y Y', ∀ x y', Q.1 x y' = cmOutputRaw C P x y'

theorem CMRel.refl {X : Type u} {Y : Type v}
    [Fintype X] [Fintype Y] (P : JointProb X Y) : CMRel P P := by
  classical
  refine ⟨CMData.identity X Y, ?_⟩
  intro x y
  simp [cmOutputRaw, CMData.identity]

/-- Forgetting normalization sends the normalized relation to the
unnormalized semiring relation. -/
theorem CMRel.toCone {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y] [Fintype Y']
    {P : JointProb X Y} {Q : JointProb X Y'} (h : CMRel P Q) :
    CMRelCone (jointProbToCone P) (jointProbToCone Q) := by
  rcases h with ⟨C, hC⟩
  refine ⟨C, Subtype.ext ?_⟩
  funext x y'
  exact hC x y'

theorem cmRel_iff_eq_output {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y] [Fintype Y']
    (P : JointProb X Y) (Q : JointProb X Y') :
    CMRel P Q ↔ ∃ C : CMData X Y Y', Q = cmOutput C P := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, Subtype.ext ?_⟩
    funext x y'
    exact hC x y'
  · rintro ⟨C, rfl⟩
    exact ⟨C, fun _ _ => rfl⟩

/-- Product of two finite embeddings. -/
def prodEmbedding {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    (eX : X ↪ X') (eY : Y ↪ Y') : X × Y ↪ X' × Y' :=
  ⟨fun p => (eX p.1, eY p.2), by
    intro a b h
    exact Prod.ext (eX.injective (congrArg Prod.fst h))
      (eY.injective (congrArg Prod.snd h))⟩

/-- Zero extension of a joint probability matrix along embeddings of both
finite alphabets. -/
noncomputable def jointZeroExtend
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    [Fintype X'] [Nonempty X'] [Fintype Y'] [Nonempty Y']
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y) : JointProb X' Y' := by
  let p : ProbVec (X × Y) :=
    ⟨fun xy => P.1 xy.1 xy.2,
     ⟨fun xy => P.2.1 xy.1 xy.2, by
       simpa only [l1Mass, Fintype.sum_prod_type] using P.2.2⟩⟩
  let q := zeroExtendProb (prodEmbedding eX eY) p
  exact ⟨fun x y => q.1 (x, y),
    ⟨fun x y => q.2.1 (x, y), by
      simpa only [l1Mass, Fintype.sum_prod_type] using q.2.2⟩⟩

@[simp] theorem jointZeroExtend_apply
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    [Fintype X'] [Nonempty X'] [Fintype Y'] [Nonempty Y']
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y) (x : X) (y : Y) :
    (jointZeroExtend eX eY P).1 (eX x) (eY y) = P.1 x y := by
  change zeroExtendRaw (prodEmbedding eX eY) (fun xy => P.1 xy.1 xy.2)
      (eX x, eY y) = P.1 x y
  simpa [prodEmbedding] using
    (zeroExtendRaw_apply (prodEmbedding eX eY)
      (fun xy => P.1 xy.1 xy.2) (x, y))

/-- The normalized and cone-valued zero extensions have the same underlying
matrix. -/
theorem jointProbToCone_jointZeroExtend
    {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    [Fintype X'] [Nonempty X'] [Fintype Y'] [Nonempty Y']
    (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y) :
    jointProbToCone (jointZeroExtend eX eY P) =
      jointConeZeroExtend eX eY (jointProbToCone P) := by
  apply Subtype.ext
  funext x y
  rfl

/-- A conditional entropy candidate defined uniformly over finite nonempty
alphabets in one universe. -/
abbrev PolyJointFunctional.{q} : Type (q + 1) :=
  ∀ {X Y : Type q}, [Fintype X] → [Nonempty X] →
    [Fintype Y] → [Nonempty Y] → JointProb X Y → ℝ

/-- Invariance under relabeling and insertion of zero rows and columns. -/
def JointEmbeddingInvariant (F : PolyJointFunctional.{u}) : Prop :=
  ∀ {X Y X' Y' : Type u},
    ∀ [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
      [Fintype X'] [Nonempty X'] [Fintype Y'] [Nonempty Y'],
      ∀ (eX : X ↪ X') (eY : Y ↪ Y') (P : JointProb X Y),
        F (jointZeroExtend eX eY P) = F P

/-- Monotonicity under fixed-row conditional mixing channels. -/
def CMMonotone (F : PolyJointFunctional.{u}) : Prop :=
  ∀ {X Y Y' : Type u},
    ∀ [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
      [Fintype Y'] [Nonempty Y'],
      ∀ (P : JointProb X Y) (Q : JointProb X Y'), CMRel P Q → F P ≤ F Q

/-- Fixed-row specialization of conditional-channel monotonicity. -/
def CMMonotoneAtRow (X : Type u) [Fintype X] [Nonempty X]
    (F : PolyJointFunctional.{u}) : Prop :=
  ∀ {Y Y' : Type u},
    ∀ [Fintype Y] [Nonempty Y] [Fintype Y'] [Nonempty Y'],
      ∀ (P : JointProb X Y) (Q : JointProb X Y'), CMRel P Q → F P ≤ F Q

/-- Conditional majorization after independent zero embeddings into finite
common alphabets. -/
def CEmbeds
    {X Y X' Y' : Type u}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    [Fintype X'] [Nonempty X'] [Fintype Y'] [Nonempty Y']
    (P : JointProb X Y) (Q : JointProb X' Y') : Prop :=
  ∃ nZ nU nV : ℕ,
    ∃ eX : X ↪ ULift.{u} (Fin (nZ + 1)),
    ∃ eX' : X' ↪ ULift.{u} (Fin (nZ + 1)),
    ∃ eY : Y ↪ ULift.{u} (Fin (nU + 1)),
    ∃ eY' : Y' ↪ ULift.{u} (Fin (nV + 1)),
      CMRel (jointZeroExtend eX eY P) (jointZeroExtend eX' eY' Q)

/-- Every finite type embeds into a strictly larger canonical finite
alphabet in the same universe. -/
noncomputable def fintypeSuccEmbedding (X : Type u) [Fintype X] :
    X ↪ ULift.{u} (Fin (Fintype.card X + 1)) where
  toFun x :=
    ⟨⟨(Fintype.equivFin X x).val,
      lt_trans (Fintype.equivFin X x).isLt (Nat.lt_succ_self _)⟩⟩
  inj' := by
    intro x x' h
    apply (Fintype.equivFin X).injective
    apply Fin.ext
    exact congrArg (fun z => z.down.val) h

theorem CEmbeds.refl
    {X Y : Type u} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (P : JointProb X Y) : CEmbeds P P := by
  let eX := fintypeSuccEmbedding X
  let eY := fintypeSuccEmbedding Y
  exact ⟨Fintype.card X, Fintype.card Y, Fintype.card Y,
    eX, eX, eY, eY, CMRel.refl (jointZeroExtend eX eY P)⟩

/-- Monotonicity for the embedded conditional-majorization relation. -/
def CEmbedsMonotone (F : PolyJointFunctional.{u}) : Prop :=
  ∀ {X Y X' Y' : Type u},
    ∀ [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
      [Fintype X'] [Nonempty X'] [Fintype Y'] [Nonempty Y'],
      ∀ (P : JointProb X Y) (Q : JointProb X' Y'), CEmbeds P Q → F P ≤ F Q

/-- Embedding invariance lifts fixed-row conditional-channel monotonicity to
the full relation between potentially different finite alphabets. -/
theorem embeddingLift (F : PolyJointFunctional.{u})
    (hemb : JointEmbeddingInvariant F) (hmono : CMMonotone F) :
    CEmbedsMonotone F := by
  intro X Y X' Y' _ _ _ _ _ _ _ _ P Q hPQ
  rcases hPQ with ⟨nZ, nU, nV, eX, eX', eY, eY', hrel⟩
  calc
    F P = F (jointZeroExtend eX eY P) :=
      (hemb (X := X) (Y := Y) (X' := ULift (Fin (nZ + 1)))
        (Y' := ULift (Fin (nU + 1)))
        eX eY P).symm
    _ ≤ F (jointZeroExtend eX' eY' Q) :=
      hmono (X := ULift (Fin (nZ + 1))) (Y := ULift (Fin (nU + 1)))
        (Y' := ULift (Fin (nV + 1)))
        _ _ hrel
    _ = F Q :=
      hemb (X := X') (Y := Y') (X' := ULift (Fin (nZ + 1)))
        (Y' := ULift (Fin (nV + 1)))
        eX' eY' Q

end ConditionalEntropy
