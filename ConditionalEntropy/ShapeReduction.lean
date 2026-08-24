import ConditionalEntropy.FiniteChannels
import ConditionalEntropy.ColumnFunctions
import ConditionalEntropy.FiniteConeSums
import ConditionalEntropy.RenyiSchur
import ConditionalEntropy.Perspective

/-!
# Conditional-channel shape reductions

This file contains the algebraic reduction from conditional-channel
monotonicity to curvature of the total column functions.  The proofs keep
zero columns explicit and use the bundled finite channel normalization.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace ConditionalEntropy

universe u v w

private theorem triple_sum_rotate
    {A : Type u} {B : Type v} {C : Type w}
    [Fintype A] [Fintype B] [Fintype C]
    (f : A → B → C → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) =
      ∑ c, ∑ b, ∑ a, f a b c := by
  let shuffle : A × (B × C) ≃ C × (B × A) :=
    { toFun := fun a => (a.2.2, (a.2.1, a.1))
      invFun := fun c => (c.2.2, (c.2.1, c.1))
      left_inv := by intro a; rfl
      right_inv := by intro c; rfl }
  calc
    (∑ a, ∑ b, ∑ c, f a b c) =
        ∑ z : A × (B × C), f z.1 z.2.1 z.2.2 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ z : C × (B × A), f z.2.2 z.2.1 z.1 := by
      exact Fintype.sum_equiv shuffle _ _ (fun _ => rfl)
    _ = ∑ c, ∑ b, ∑ a, f a b c := by
      simp only [Fintype.sum_prod_type]

private theorem sum_ulift
    {A : Type v} [Fintype A] (f : ULift.{u, v} A → ℝ) :
    (∑ a, f a) = ∑ a : A, f (ULift.up a) := by
  exact Fintype.sum_equiv Equiv.ulift _ _ (fun _ => rfl)

/-! ## The normalized two-column merge -/

/-- A two-column joint distribution obtained by normalizing two weighted cone
vectors by their common total mass. -/
def normalizedTwoColumn
    {I : Type u} [Fintype I]
    (x z : ConeVec I) (lambda : ℝ)
    (hlambda : lambda ∈ Icc (0 : ℝ) 1)
    (hm : 0 < l1Mass (coneMix lambda hlambda x z).1) :
    JointProb I (ULift.{u} (Fin 2)) := by
  classical
  let m := l1Mass (coneMix lambda hlambda x z).1
  refine ⟨fun i j => if j.down = 0 then lambda * x.1 i / m
      else (1 - lambda) * z.1 i / m, ?_, ?_⟩
  · intro i j
    change 0 ≤ if j.down = 0 then lambda * x.1 i / m
      else (1 - lambda) * z.1 i / m
    split_ifs
    · exact div_nonneg (mul_nonneg hlambda.1 (x.2 i)) hm.le
    · exact div_nonneg (mul_nonneg (sub_nonneg.mpr hlambda.2) (z.2 i)) hm.le
  · change ∑ i, ∑ j : ULift.{u} (Fin 2),
      (if j.down = 0 then lambda * x.1 i / m
        else (1 - lambda) * z.1 i / m) = 1
    simp_rw [sum_ulift, Fin.sum_univ_two]
    simp only [if_pos, one_ne_zero, if_false]
    rw [Finset.sum_add_distrib]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.sum_mul,
      ← Finset.mul_sum, ← Finset.mul_sum]
    rw [← add_mul]
    change (lambda * l1Mass x.1 + (1 - lambda) * l1Mass z.1) * m⁻¹ = 1
    rw [← div_eq_mul_inv]
    rw [← l1Mass_coneMix]
    exact div_self hm.ne'

/-- The first normalized column is the expected scaled cone vector. -/
theorem normalizedTwoColumn_column_zero
    {I : Type u} [Fintype I]
    (x z : ConeVec I) (lambda : ℝ)
    (hlambda : lambda ∈ Icc (0 : ℝ) 1)
    (hm : 0 < l1Mass (coneMix lambda hlambda x z).1) :
    column (normalizedTwoColumn x z lambda hlambda hm)
      (ULift.up (0 : Fin 2)) =
      coneScale
        (lambda / l1Mass (coneMix lambda hlambda x z).1)
        (div_nonneg hlambda.1 hm.le) x := by
  apply Subtype.ext
  funext i
  change lambda * x.1 i / l1Mass (coneMix lambda hlambda x z).1 =
    (lambda / l1Mass (coneMix lambda hlambda x z).1) * x.1 i
  ring

/-- The second normalized column is the expected scaled cone vector. -/
theorem normalizedTwoColumn_column_one
    {I : Type u} [Fintype I]
    (x z : ConeVec I) (lambda : ℝ)
    (hlambda : lambda ∈ Icc (0 : ℝ) 1)
    (hm : 0 < l1Mass (coneMix lambda hlambda x z).1) :
    column (normalizedTwoColumn x z lambda hlambda hm)
      (ULift.up (1 : Fin 2)) =
      coneScale
        ((1 - lambda) / l1Mass (coneMix lambda hlambda x z).1)
        (div_nonneg (sub_nonneg.mpr hlambda.2) hm.le) z := by
  apply Subtype.ext
  funext i
  change (1 - lambda) * z.1 i /
      l1Mass (coneMix lambda hlambda x z).1 =
    ((1 - lambda) / l1Mass (coneMix lambda hlambda x z).1) * z.1 i
  ring

/-- The one-branch channel which merges both input columns. -/
def mergeTwoChannel (I : Type u) [Fintype I] :
    CMData I (ULift.{u} (Fin 2)) (ULift.{u} Unit) := by
  classical
  exact
  { n := 1
    n_pos := by norm_num
    S := fun _ i j => if i = j then 1 else 0
    hS := by
      intro k
      exact ⟨by
        intro i j
        change 0 ≤ if i = j then 1 else 0
        split_ifs <;> norm_num, by
        intro i
        simp, by
        intro j
        simp⟩
    D := fun _ _ _ => 1
    hD := by intro k y u; norm_num
    hnorm := by simp }

/-- The sole output of the merge channel is the normalized cone mixture. -/
theorem mergeTwoChannel_output_column
    {I : Type u} [Fintype I]
    (x z : ConeVec I) (lambda : ℝ)
    (hlambda : lambda ∈ Icc (0 : ℝ) 1)
    (hm : 0 < l1Mass (coneMix lambda hlambda x z).1) :
    column (cmOutput (mergeTwoChannel I)
      (normalizedTwoColumn x z lambda hlambda hm)) (ULift.up ()) =
      coneScale (1 / l1Mass (coneMix lambda hlambda x z).1)
        (div_nonneg zero_le_one hm.le)
        (coneMix lambda hlambda x z) := by
  classical
  apply Subtype.ext
  funext i
  change (∑ k : Fin 1, ∑ y : ULift.{u} (Fin 2), ∑ j,
    (if i = j then 1 else 0) *
      (if y.down = 0 then lambda * x.1 j /
        l1Mass (coneMix lambda hlambda x z).1
      else (1 - lambda) * z.1 j /
        l1Mass (coneMix lambda hlambda x z).1) * 1) =
    (1 / l1Mass (coneMix lambda hlambda x z).1) *
      (lambda * x.1 i + (1 - lambda) * z.1 i)
  simp_rw [sum_ulift]
  simp [Fin.sum_univ_two]
  ring

/-- The sum of a degree-one function over the normalized input columns is a
common inverse-mass multiple of its desired concavity expression. -/
theorem sum_normalizedTwoColumn
    {I : Type u} [Fintype I]
    (F : ConeVec I → ℝ) (hF : PosHomOne F)
    (x z : ConeVec I) (lambda : ℝ)
    (hlambda : lambda ∈ Icc (0 : ℝ) 1)
    (hm : 0 < l1Mass (coneMix lambda hlambda x z).1) :
    (∑ y : ULift.{u} (Fin 2), F (column
      (normalizedTwoColumn x z lambda hlambda hm) y)) =
      (1 / l1Mass (coneMix lambda hlambda x z).1) *
        (lambda * F x + (1 - lambda) * F z) := by
  rw [sum_ulift, Fin.sum_univ_two, normalizedTwoColumn_column_zero,
    normalizedTwoColumn_column_one,
    hF x (lambda / l1Mass (coneMix lambda hlambda x z).1)
      (div_nonneg hlambda.1 hm.le),
    hF z ((1 - lambda) / l1Mass (coneMix lambda hlambda x z).1)
      (div_nonneg (sub_nonneg.mpr hlambda.2) hm.le)]
  ring

/-- The sum of a degree-one function over the sole merged output column is a
common inverse-mass multiple of its value on the mixture. -/
theorem sum_mergeTwoChannel_output
    {I : Type u} [Fintype I]
    (F : ConeVec I → ℝ) (hF : PosHomOne F)
    (x z : ConeVec I) (lambda : ℝ)
    (hlambda : lambda ∈ Icc (0 : ℝ) 1)
    (hm : 0 < l1Mass (coneMix lambda hlambda x z).1) :
    (∑ y : ULift.{u} Unit, F (column (cmOutput (mergeTwoChannel I)
      (normalizedTwoColumn x z lambda hlambda hm)) y)) =
      (1 / l1Mass (coneMix lambda hlambda x z).1) *
        F (coneMix lambda hlambda x z) := by
  rw [sum_ulift, Fintype.sum_unique, mergeTwoChannel_output_column,
    hF (coneMix lambda hlambda x z)
      (1 / l1Mass (coneMix lambda hlambda x z).1)
      (div_nonneg zero_le_one hm.le)]

/-- An interior cone mixture can vanish only when both summands vanish. -/
theorem eq_zero_pair_of_coneMix_eq_zero
    {I : Type u} [Finite I]
    (x z : ConeVec I) (lambda : ℝ)
    (hlambda : lambda ∈ Icc (0 : ℝ) 1)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (hmix : coneMix lambda hlambda x z = 0) :
    x = 0 ∧ z = 0 := by
  letI := Fintype.ofFinite I
  have hmx : 0 ≤ l1Mass x.1 := Finset.sum_nonneg fun i _ => x.2 i
  have hmz : 0 ≤ l1Mass z.1 := Finset.sum_nonneg fun i _ => z.2 i
  have hmass : lambda * l1Mass x.1 +
      (1 - lambda) * l1Mass z.1 = 0 := by
    rw [← l1Mass_coneMix lambda hlambda x z, hmix]
    simp [l1Mass]
  have hmx0 : l1Mass x.1 = 0 := by nlinarith
  have hmz0 : l1Mass z.1 = 0 := by nlinarith
  constructor
  · apply Subtype.ext
    exact (nonzeroMass x.1 x.2).1.mp hmx0
  · apply Subtype.ext
    exact (nonzeroMass z.1 z.2).1.mp hmz0

/-! ## Schur monotonicity after positive integration -/

/-- Positive integration preserves the Schur-concavity inequality for the
endpoint-aware Renyi family. -/
theorem integratedEntropyPos_probMatrixAction
    {I : Type u} [Fintype I] [Nonempty I]
    (ν : Measure Param) [IsFiniteMeasure ν]
    (S : I → I → ℝ) (hS : DoublyStochastic S) (p : ProbVec I) :
    integratedEntropyPos ν p ≤
      integratedEntropyPos ν (probMatrixAction S hS p) := by
  unfold integratedEntropyPos
  exact integral_mono (integrable_renyi ν p)
    (integrable_renyi ν (probMatrixAction S hS p))
    (fun a => renyiSchur S hS p a)

/-- A doubly stochastic action on a nonzero cone vector remains nonzero. -/
theorem coneMatrixAction_ne_zero
    {I : Type u} [Fintype I]
    (S : I → I → ℝ) (hS : DoublyStochastic S)
    (x : ConeVec I) (hx : x ≠ 0) :
    coneMatrixAction S hS.1 x ≠ 0 := by
  apply (coneNonzeroMass (coneMatrixAction S hS.1 x)).mpr
  rw [doublyStochastic_mass S hS]
  exact (coneNonzeroMass x).mp hx

/-- Normalization commutes with a doubly stochastic action. -/
theorem normalize_coneMatrixAction
    {I : Type u} [Fintype I] [Nonempty I]
    (S : I → I → ℝ) (hS : DoublyStochastic S)
    (x : ConeVec I) (hx : x ≠ 0) :
    normalize (toPosCone (coneMatrixAction S hS.1 x)
      (coneMatrixAction_ne_zero S hS x hx)) =
      probMatrixAction S hS (normalize (toPosCone x hx)) := by
  apply Subtype.ext
  funext i
  have hm : 0 < l1Mass x.1 := (coneNonzeroMass x).mp hx
  change (∑ j, S i j * x.1 j) /
      l1Mass (coneMatrixAction S hS.1 x).1 =
    ∑ j, S i j * (x.1 j / l1Mass x.1)
  rw [doublyStochastic_mass S hS]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The integrated entropy of the normalization of a nonzero cone vector
cannot decrease under a doubly stochastic action. -/
theorem integratedEntropyPos_normalize_coneMatrixAction
    {I : Type u} [Fintype I] [Nonempty I]
    (ν : Measure Param) [IsFiniteMeasure ν]
    (S : I → I → ℝ) (hS : DoublyStochastic S)
    (x : ConeVec I) (hx : x ≠ 0) :
    integratedEntropyPos ν (normalize (toPosCone x hx)) ≤
      integratedEntropyPos ν
        (normalize (toPosCone (coneMatrixAction S hS.1 x)
          (coneMatrixAction_ne_zero S hS x hx))) := by
  rw [normalize_coneMatrixAction S hS x hx]
  exact integratedEntropyPos_probMatrixAction ν S hS _

/-! ## Exact output-column decomposition -/

@[simp] theorem coneSum_apply
    {I : Type u} {J : Type v} [Fintype J]
    (z : J → ConeVec I) (i : I) :
    (coneSum z).1 i = ∑ j, (z j).1 i := by
  simp [coneSum]

/-- One output column is the finite sum of the scaled, doubly stochastic
images of all input columns. -/
theorem cmOutput_column_decomposition
    {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Fintype Y] [Fintype Y']
    (C : CMData X Y Y') (P : JointProb X Y) (y' : Y') :
    column (cmOutput C P) y' =
      coneSum (fun ky : Fin C.n × Y =>
        coneScale (C.D ky.1 ky.2 y') (C.hD ky.1 ky.2 y')
          (coneMatrixAction (C.S ky.1) (C.hS ky.1).1
            (column P ky.2))) := by
  apply Subtype.ext
  funext x
  rw [coneSum_apply]
  change (∑ k, ∑ y, ∑ z, C.S k x z * P.1 z y * C.D k y y') =
    ∑ ky : Fin C.n × Y,
      C.D ky.1 ky.2 y' * ∑ z, C.S ky.1 x z * P.1 z ky.2
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-! ## Column-function Schur inequalities -/

theorem columnPhi_coneMatrixAction_ge
    {I : Type u} [Fintype I] [Nonempty I]
    (t : ℝ) (ht : 0 < t) (τ : ProbabilityMeasure Param)
    (S : I → I → ℝ) (hS : DoublyStochastic S) (x : ConeVec I) :
    columnPhi t τ x ≤ columnPhi t τ (coneMatrixAction S hS.1 x) := by
  by_cases hx : x = 0
  · subst x
    have hz : coneMatrixAction S hS.1 (0 : ConeVec I) = 0 := by
      apply Subtype.ext
      funext i
      simp [coneMatrixAction_apply]
    rw [hz]
  have hSx := coneMatrixAction_ne_zero S hS x hx
  letI : IsFiniteMeasure (probMeasure τ) := by
    unfold probMeasure
    infer_instance
  have hA := integratedEntropyPos_normalize_coneMatrixAction
    (probMeasure τ) S hS x hx
  have htA := mul_le_mul_of_nonneg_left hA ht.le
  have hexp := Real.exp_le_exp.mpr htA
  rw [columnPhi_of_ne t τ x hx, columnPhi_of_ne t τ _ hSx,
    doublyStochastic_mass S hS]
  exact mul_le_mul_of_nonneg_left hexp
    (Finset.sum_nonneg fun i _ => x.2 i)

theorem columnPhi_coneMatrixAction_le
    {I : Type u} [Fintype I] [Nonempty I]
    (t : ℝ) (ht : t < 0) (τ : ProbabilityMeasure Param)
    (S : I → I → ℝ) (hS : DoublyStochastic S) (x : ConeVec I) :
    columnPhi t τ (coneMatrixAction S hS.1 x) ≤ columnPhi t τ x := by
  by_cases hx : x = 0
  · subst x
    have hz : coneMatrixAction S hS.1 (0 : ConeVec I) = 0 := by
      apply Subtype.ext
      funext i
      simp [coneMatrixAction_apply]
    rw [hz]
  have hSx := coneMatrixAction_ne_zero S hS x hx
  letI : IsFiniteMeasure (probMeasure τ) := by
    unfold probMeasure
    infer_instance
  have hA := integratedEntropyPos_normalize_coneMatrixAction
    (probMeasure τ) S hS x hx
  have htA := mul_le_mul_of_nonpos_left hA ht.le
  have hexp := Real.exp_le_exp.mpr htA
  rw [columnPhi_of_ne t τ x hx, columnPhi_of_ne t τ _ hSx,
    doublyStochastic_mass S hS]
  exact mul_le_mul_of_nonneg_left hexp
    (Finset.sum_nonneg fun i _ => x.2 i)

theorem columnDeriv_coneMatrixAction_ge
    {I : Type u} [Fintype I] [Nonempty I]
    (σ : FiniteMeasure Param)
    (S : I → I → ℝ) (hS : DoublyStochastic S) (x : ConeVec I) :
    columnDeriv σ x ≤ columnDeriv σ (coneMatrixAction S hS.1 x) := by
  by_cases hx : x = 0
  · subst x
    have hz : coneMatrixAction S hS.1 (0 : ConeVec I) = 0 := by
      apply Subtype.ext
      funext i
      simp [coneMatrixAction_apply]
    rw [hz]
  have hSx := coneMatrixAction_ne_zero S hS x hx
  letI : IsFiniteMeasure (finiteMeasure σ) := by
    unfold finiteMeasure
    infer_instance
  have hA := integratedEntropyPos_normalize_coneMatrixAction
    (finiteMeasure σ) S hS x hx
  rw [columnDeriv_of_ne σ x hx, columnDeriv_of_ne σ _ hSx,
    doublyStochastic_mass S hS]
  exact mul_le_mul_of_nonneg_left hA
    (Finset.sum_nonneg fun i _ => x.2 i)

/-- Doubly stochastic action on the punctured cone. -/
def posConeMatrixAction
    {I : Type u} [Fintype I]
    (S : I → I → ℝ) (hS : DoublyStochastic S)
    (x : PosConeVec I) : PosConeVec I :=
  toPosCone (coneMatrixAction S hS.1 x.1)
    (coneMatrixAction_ne_zero S hS x.1 (by
      intro hx
      apply x.2
      exact congrArg Subtype.val hx))

/-- The positive tropical column function is Schur increasing. -/
theorem aTrop_posConeMatrixAction_ge
    {I : Type u} [Fintype I] [Nonempty I]
    (τ : ProbabilityMeasure Param)
    (S : I → I → ℝ) (hS : DoublyStochastic S)
    (x : PosConeVec I) :
    aTrop τ x ≤ aTrop τ (posConeMatrixAction S hS x) := by
  letI : IsFiniteMeasure (probMeasure τ) := by
    unfold probMeasure
    infer_instance
  have hx : x.1 ≠ 0 := by
    intro hx
    apply x.2
    exact congrArg Subtype.val hx
  exact integratedEntropyPos_normalize_coneMatrixAction
    (probMeasure τ) S hS x.1 hx

/-- The negative tropical column function is Schur decreasing. -/
theorem gTrop_posConeMatrixAction_le
    {I : Type u} [Fintype I] [Nonempty I]
    (τ : ProbabilityMeasure Param)
    (S : I → I → ℝ) (hS : DoublyStochastic S)
    (x : PosConeVec I) :
    gTrop τ (posConeMatrixAction S hS x) ≤ gTrop τ x := by
  exact neg_le_neg (aTrop_posConeMatrixAction_ge τ S hS x)

/-! ## Finite channel mixing of homogeneous column functions -/

/-- A concave, degree-one column function which is Schur increasing has a
nondecreasing sum under every conditional channel. -/
theorem cmOutput_sum_ge_of_concave
    {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Nonempty X] [Fintype Y] [Fintype Y']
    (F : ConeVec X → ℝ) (hF : PosHomOne F) (hconc : ConcaveCone F)
    (hSchur : ∀ (S : X → X → ℝ) (hS : DoublyStochastic S)
      (x : ConeVec X), F x ≤ F (coneMatrixAction S hS.1 x))
    (C : CMData X Y Y') (P : JointProb X Y) :
    (∑ y : Y, F (column P y)) ≤
      ∑ y' : Y', F (column (cmOutput C P) y') := by
  classical
  have hper (y' : Y') :
      (∑ ky : Fin C.n × Y,
        C.D ky.1 ky.2 y' *
          F (coneMatrixAction (C.S ky.1) (C.hS ky.1).1
            (column P ky.2))) ≤
        F (column (cmOutput C P) y') := by
    rw [cmOutput_column_decomposition C P y']
    calc
      (∑ ky : Fin C.n × Y,
          C.D ky.1 ky.2 y' *
            F (coneMatrixAction (C.S ky.1) (C.hS ky.1).1
              (column P ky.2))) =
          ∑ ky : Fin C.n × Y,
            F (coneScale (C.D ky.1 ky.2 y') (C.hD ky.1 ky.2 y')
              (coneMatrixAction (C.S ky.1) (C.hS ky.1).1
                (column P ky.2))) := by
        apply Finset.sum_congr rfl
        intro ky _
        exact (hF _ _ (C.hD ky.1 ky.2 y')).symm
      _ ≤ F (coneSum (fun ky : Fin C.n × Y =>
          coneScale (C.D ky.1 ky.2 y') (C.hD ky.1 ky.2 y')
            (coneMatrixAction (C.S ky.1) (C.hS ky.1).1
              (column P ky.2)))) :=
        concaveCone_sum_le F hF hconc _
  calc
    (∑ y : Y, F (column P y)) =
        ∑ y : Y, ∑ k : Fin C.n, ∑ y' : Y',
          C.D k y y' * F (column P y) := by
      apply Finset.sum_congr rfl
      intro y _
      calc
        F (column P y) = 1 * F (column P y) := (one_mul _).symm
        _ = (∑ k, ∑ y', C.D k y y') * F (column P y) := by
          rw [C.hnorm y]
        _ = ∑ k, (∑ y', C.D k y y') * F (column P y) := by
          rw [Finset.sum_mul]
        _ = ∑ k, ∑ y', C.D k y y' * F (column P y) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
    _ ≤ ∑ y : Y, ∑ k : Fin C.n, ∑ y' : Y',
          C.D k y y' *
            F (coneMatrixAction (C.S k) (C.hS k).1 (column P y)) := by
      apply Finset.sum_le_sum
      intro y _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro y' _
      exact mul_le_mul_of_nonneg_left
        (hSchur (C.S k) (C.hS k) (column P y)) (C.hD k y y')
    _ = ∑ y' : Y', ∑ ky : Fin C.n × Y,
          C.D ky.1 ky.2 y' *
            F (coneMatrixAction (C.S ky.1) (C.hS ky.1).1
              (column P ky.2)) := by
      simp only [Fintype.sum_prod_type]
      exact triple_sum_rotate (fun y k y' => C.D k y y' *
        F (coneMatrixAction (C.S k) (C.hS k).1 (column P y)))
    _ ≤ ∑ y' : Y', F (column (cmOutput C P) y') :=
      Finset.sum_le_sum fun y' _ => hper y'

/-- A convex, degree-one column function which is Schur decreasing has a
nonincreasing sum under every conditional channel. -/
theorem cmOutput_sum_le_of_convex
    {X : Type u} {Y : Type v} {Y' : Type w}
    [Fintype X] [Nonempty X] [Fintype Y] [Fintype Y']
    (F : ConeVec X → ℝ) (hF : PosHomOne F) (hconv : ConvexCone F)
    (hSchur : ∀ (S : X → X → ℝ) (hS : DoublyStochastic S)
      (x : ConeVec X),
        F (coneMatrixAction S hS.1 x) ≤ F x)
    (C : CMData X Y Y') (P : JointProb X Y) :
    (∑ y' : Y', F (column (cmOutput C P) y')) ≤
      ∑ y : Y, F (column P y) := by
  classical
  have hper (y' : Y') :
      F (column (cmOutput C P) y') ≤
        ∑ ky : Fin C.n × Y,
          C.D ky.1 ky.2 y' *
            F (coneMatrixAction (C.S ky.1) (C.hS ky.1).1
              (column P ky.2)) := by
    rw [cmOutput_column_decomposition C P y']
    calc
      F (coneSum (fun ky : Fin C.n × Y =>
          coneScale (C.D ky.1 ky.2 y') (C.hD ky.1 ky.2 y')
            (coneMatrixAction (C.S ky.1) (C.hS ky.1).1
              (column P ky.2)))) ≤
          ∑ ky : Fin C.n × Y,
            F (coneScale (C.D ky.1 ky.2 y') (C.hD ky.1 ky.2 y')
              (coneMatrixAction (C.S ky.1) (C.hS ky.1).1
                (column P ky.2))) :=
        convexCone_sum_le F hF hconv _
      _ = ∑ ky : Fin C.n × Y,
          C.D ky.1 ky.2 y' *
            F (coneMatrixAction (C.S ky.1) (C.hS ky.1).1
              (column P ky.2)) := by
        apply Finset.sum_congr rfl
        intro ky _
        exact hF _ _ (C.hD ky.1 ky.2 y')
  calc
    (∑ y' : Y', F (column (cmOutput C P) y')) ≤
        ∑ y' : Y', ∑ ky : Fin C.n × Y,
          C.D ky.1 ky.2 y' *
            F (coneMatrixAction (C.S ky.1) (C.hS ky.1).1
              (column P ky.2)) :=
      Finset.sum_le_sum fun y' _ => hper y'
    _ = ∑ y : Y, ∑ k : Fin C.n, ∑ y' : Y',
          C.D k y y' *
            F (coneMatrixAction (C.S k) (C.hS k).1 (column P y)) := by
      simp only [Fintype.sum_prod_type]
      exact (triple_sum_rotate (fun y k y' => C.D k y y' *
        F (coneMatrixAction (C.S k) (C.hS k).1 (column P y)))).symm
    _ ≤ ∑ y : Y, ∑ k : Fin C.n, ∑ y' : Y',
          C.D k y y' * F (column P y) := by
      apply Finset.sum_le_sum
      intro y _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro y' _
      exact mul_le_mul_of_nonneg_left
        (hSchur (C.S k) (C.hS k) (column P y)) (C.hD k y y')
    _ = ∑ y : Y, F (column P y) := by
      apply Finset.sum_congr rfl
      intro y _
      calc
        (∑ k, ∑ y', C.D k y y' * F (column P y)) =
            ∑ k, (∑ y', C.D k y y') * F (column P y) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
        _ = (∑ k, ∑ y', C.D k y y') * F (column P y) := by
          rw [Finset.sum_mul]
        _ = F (column P y) := by rw [C.hnorm y, one_mul]

/-! ## Forward rowwise shape reductions -/

/-- Fixed-row monotonicity at positive temperature forces concavity of the
total exponential column perspective.  The proof uses the normalized
two-column merge above. -/
theorem concave_columnPhi_of_cmMonotoneAtRow
    (X : Type u) [Fintype X] [Nonempty X]
    (t : ℝ) (ht : 0 < t) (τ : ProbabilityMeasure Param)
    (hmono : CMMonotoneAtRow X (HTemp t ht.ne' τ)) :
    ConcaveCone (columnPhi t τ : ConeVec X → ℝ) := by
  intro x z lambda hlambda
  by_cases hl0 : lambda = 0
  · subst lambda
    simp [coneMix]
  by_cases hl1 : lambda = 1
  · subst lambda
    simp [coneMix]
  have hlpos : 0 < lambda := lt_of_le_of_ne hlambda.1 (Ne.symm hl0)
  have hllt : lambda < 1 := lt_of_le_of_ne hlambda.2 hl1
  by_cases hmix : coneMix lambda hlambda x z = 0
  · obtain ⟨rfl, rfl⟩ :=
      eq_zero_pair_of_coneMix_eq_zero x z lambda hlambda hlpos hllt hmix
    have hzero : coneMix lambda hlambda (0 : ConeVec X) 0 = 0 := by
      apply Subtype.ext
      funext i
      simp [coneMix]
    rw [hzero, columnPhi_zero]
    norm_num
  · have hm : 0 < l1Mass (coneMix lambda hlambda x z).1 :=
      (coneNonzeroMass (coneMix lambda hlambda x z)).mp hmix
    let P := normalizedTwoColumn x z lambda hlambda hm
    have hrel : CMRel P (cmOutput (mergeTwoChannel X) P) :=
      ⟨mergeTwoChannel X, fun _ _ => rfl⟩
    have hH : HTemp t ht.ne' τ P ≤
        HTemp t ht.ne' τ (cmOutput (mergeTwoChannel X) P) :=
      @hmono (ULift.{u} (Fin 2)) (ULift.{u} Unit)
        inferInstance inferInstance inferInstance
        inferInstance P (cmOutput (mergeTwoChannel X) P) hrel
    have hmul : t * HTemp t ht.ne' τ P ≤
        t * HTemp t ht.ne' τ (cmOutput (mergeTwoChannel X) P) :=
      mul_le_mul_of_nonneg_left hH ht.le
    have hexp := Real.exp_le_exp.mpr hmul
    rw [← sum_columnPhi_eq_exp_HTemp t ht.ne' τ P,
      ← sum_columnPhi_eq_exp_HTemp t ht.ne' τ
        (cmOutput (mergeTwoChannel X) P)] at hexp
    change (∑ y : ULift.{u} (Fin 2), columnPhi t τ (column
      (normalizedTwoColumn x z lambda hlambda hm) y)) ≤
      ∑ y : ULift.{u} Unit, columnPhi t τ (column
        (cmOutput (mergeTwoChannel X)
          (normalizedTwoColumn x z lambda hlambda hm)) y) at hexp
    rw [sum_normalizedTwoColumn (columnPhi t τ)
      (columnPhi_posHomOne t τ) x z lambda hlambda hm,
      sum_mergeTwoChannel_output (columnPhi t τ)
        (columnPhi_posHomOne t τ) x z lambda hlambda hm] at hexp
    exact le_of_mul_le_mul_left hexp (one_div_pos.mpr hm)

/-- Concavity of the positive-temperature column perspective implies
conditional-channel monotonicity at the fixed row alphabet. -/
theorem cmMonotoneAtRow_HTemp_of_concave
    (X : Type u) [Fintype X] [Nonempty X]
    (t : ℝ) (ht : 0 < t) (τ : ProbabilityMeasure Param)
    (hconc : ConcaveCone (columnPhi t τ : ConeVec X → ℝ)) :
    CMMonotoneAtRow X (HTemp t ht.ne' τ) := by
  intro Y Y' _ _ _ _ P Q hPQ
  rcases (cmRel_iff_eq_output P Q).mp hPQ with ⟨C, rfl⟩
  have hsum := cmOutput_sum_ge_of_concave
    (columnPhi t τ : ConeVec X → ℝ) (columnPhi_posHomOne t τ) hconc
    (columnPhi_coneMatrixAction_ge t ht τ) C P
  rw [sum_columnPhi_eq_exp_HTemp t ht.ne' τ P,
    sum_columnPhi_eq_exp_HTemp t ht.ne' τ (cmOutput C P)] at hsum
  have hmul : t * HTemp t ht.ne' τ P ≤
      t * HTemp t ht.ne' τ (cmOutput C P) := Real.exp_le_exp.mp hsum
  nlinarith

/-- Fixed-row monotonicity at negative temperature forces convexity of the
total exponential column perspective. -/
theorem convex_columnPhi_of_cmMonotoneAtRow
    (X : Type u) [Fintype X] [Nonempty X]
    (t : ℝ) (ht : t < 0) (τ : ProbabilityMeasure Param)
    (hmono : CMMonotoneAtRow X (HTemp t ht.ne τ)) :
    ConvexCone (columnPhi t τ : ConeVec X → ℝ) := by
  intro x z lambda hlambda
  by_cases hl0 : lambda = 0
  · subst lambda
    simp [coneMix]
  by_cases hl1 : lambda = 1
  · subst lambda
    simp [coneMix]
  have hlpos : 0 < lambda := lt_of_le_of_ne hlambda.1 (Ne.symm hl0)
  have hllt : lambda < 1 := lt_of_le_of_ne hlambda.2 hl1
  by_cases hmix : coneMix lambda hlambda x z = 0
  · obtain ⟨rfl, rfl⟩ :=
      eq_zero_pair_of_coneMix_eq_zero x z lambda hlambda hlpos hllt hmix
    have hzero : coneMix lambda hlambda (0 : ConeVec X) 0 = 0 := by
      apply Subtype.ext
      funext i
      simp [coneMix]
    rw [hzero, columnPhi_zero]
    norm_num
  · have hm : 0 < l1Mass (coneMix lambda hlambda x z).1 :=
      (coneNonzeroMass (coneMix lambda hlambda x z)).mp hmix
    let P := normalizedTwoColumn x z lambda hlambda hm
    have hrel : CMRel P (cmOutput (mergeTwoChannel X) P) :=
      ⟨mergeTwoChannel X, fun _ _ => rfl⟩
    have hH : HTemp t ht.ne τ P ≤
        HTemp t ht.ne τ (cmOutput (mergeTwoChannel X) P) :=
      @hmono (ULift.{u} (Fin 2)) (ULift.{u} Unit)
        inferInstance inferInstance inferInstance inferInstance
        P (cmOutput (mergeTwoChannel X) P) hrel
    have hmul : t * HTemp t ht.ne τ (cmOutput (mergeTwoChannel X) P) ≤
        t * HTemp t ht.ne τ P :=
      mul_le_mul_of_nonpos_left hH ht.le
    have hexp := Real.exp_le_exp.mpr hmul
    rw [← sum_columnPhi_eq_exp_HTemp t ht.ne τ
        (cmOutput (mergeTwoChannel X) P),
      ← sum_columnPhi_eq_exp_HTemp t ht.ne τ P] at hexp
    change (∑ y : ULift.{u} Unit, columnPhi t τ (column
      (cmOutput (mergeTwoChannel X)
        (normalizedTwoColumn x z lambda hlambda hm)) y)) ≤
      ∑ y : ULift.{u} (Fin 2), columnPhi t τ (column
        (normalizedTwoColumn x z lambda hlambda hm) y) at hexp
    rw [sum_mergeTwoChannel_output (columnPhi t τ)
        (columnPhi_posHomOne t τ) x z lambda hlambda hm,
      sum_normalizedTwoColumn (columnPhi t τ)
        (columnPhi_posHomOne t τ) x z lambda hlambda hm] at hexp
    exact le_of_mul_le_mul_left hexp (one_div_pos.mpr hm)

/-- Convexity of the negative-temperature column perspective implies
conditional-channel monotonicity at the fixed row alphabet. -/
theorem cmMonotoneAtRow_HTemp_of_convex
    (X : Type u) [Fintype X] [Nonempty X]
    (t : ℝ) (ht : t < 0) (τ : ProbabilityMeasure Param)
    (hconv : ConvexCone (columnPhi t τ : ConeVec X → ℝ)) :
    CMMonotoneAtRow X (HTemp t ht.ne τ) := by
  intro Y Y' _ _ _ _ P Q hPQ
  rcases (cmRel_iff_eq_output P Q).mp hPQ with ⟨C, rfl⟩
  have hsum := cmOutput_sum_le_of_convex
    (columnPhi t τ : ConeVec X → ℝ) (columnPhi_posHomOne t τ) hconv
    (columnPhi_coneMatrixAction_le t ht τ) C P
  rw [sum_columnPhi_eq_exp_HTemp t ht.ne τ (cmOutput C P),
    sum_columnPhi_eq_exp_HTemp t ht.ne τ P] at hsum
  have hmul : t * HTemp t ht.ne τ (cmOutput C P) ≤
      t * HTemp t ht.ne τ P := Real.exp_le_exp.mp hsum
  nlinarith

/-- Concavity of the derivation perspective implies fixed-row
conditional-channel monotonicity. -/
theorem cmMonotoneAtRow_HZero_of_concave
    (X : Type u) [Fintype X] [Nonempty X]
    (σ : FiniteMeasure Param)
    (hconc : ConcaveCone (columnDeriv σ : ConeVec X → ℝ)) :
    CMMonotoneAtRow X (HZero σ) := by
  intro Y Y' _ _ _ _ P Q hPQ
  rcases (cmRel_iff_eq_output P Q).mp hPQ with ⟨C, rfl⟩
  have hsum := cmOutput_sum_ge_of_concave
    (columnDeriv σ : ConeVec X → ℝ) (columnDeriv_posHomOne σ) hconc
    (columnDeriv_coneMatrixAction_ge σ) C P
  simpa only [sum_columnDeriv_eq_HZero] using hsum

/-- Fixed-row monotonicity of the derivation candidate forces concavity of
its total linear perspective. -/
theorem concave_columnDeriv_of_cmMonotoneAtRow
    (X : Type u) [Fintype X] [Nonempty X]
    (σ : FiniteMeasure Param)
    (hmono : CMMonotoneAtRow X (HZero σ)) :
    ConcaveCone (columnDeriv σ : ConeVec X → ℝ) := by
  intro x z lambda hlambda
  by_cases hl0 : lambda = 0
  · subst lambda
    simp [coneMix]
  by_cases hl1 : lambda = 1
  · subst lambda
    simp [coneMix]
  have hlpos : 0 < lambda := lt_of_le_of_ne hlambda.1 (Ne.symm hl0)
  have hllt : lambda < 1 := lt_of_le_of_ne hlambda.2 hl1
  by_cases hmix : coneMix lambda hlambda x z = 0
  · obtain ⟨rfl, rfl⟩ :=
      eq_zero_pair_of_coneMix_eq_zero x z lambda hlambda hlpos hllt hmix
    have hzero : coneMix lambda hlambda (0 : ConeVec X) 0 = 0 := by
      apply Subtype.ext
      funext i
      simp [coneMix]
    rw [hzero, columnDeriv_zero]
    norm_num
  · have hm : 0 < l1Mass (coneMix lambda hlambda x z).1 :=
      (coneNonzeroMass (coneMix lambda hlambda x z)).mp hmix
    let P := normalizedTwoColumn x z lambda hlambda hm
    have hrel : CMRel P (cmOutput (mergeTwoChannel X) P) :=
      ⟨mergeTwoChannel X, fun _ _ => rfl⟩
    have hH : HZero σ P ≤ HZero σ (cmOutput (mergeTwoChannel X) P) :=
      @hmono (ULift.{u} (Fin 2)) (ULift.{u} Unit)
        inferInstance inferInstance inferInstance inferInstance
        P (cmOutput (mergeTwoChannel X) P) hrel
    rw [← sum_columnDeriv_eq_HZero σ P,
      ← sum_columnDeriv_eq_HZero σ (cmOutput (mergeTwoChannel X) P)] at hH
    change (∑ y : ULift.{u} (Fin 2), columnDeriv σ (column
      (normalizedTwoColumn x z lambda hlambda hm) y)) ≤
      ∑ y : ULift.{u} Unit, columnDeriv σ (column
        (cmOutput (mergeTwoChannel X)
          (normalizedTwoColumn x z lambda hlambda hm)) y) at hH
    rw [sum_normalizedTwoColumn (columnDeriv σ)
        (columnDeriv_posHomOne σ) x z lambda hlambda hm,
      sum_mergeTwoChannel_output (columnDeriv σ)
        (columnDeriv_posHomOne σ) x z lambda hlambda hm] at hH
    exact le_of_mul_le_mul_left hH (one_div_pos.mpr hm)

/-- Exact fixed-row temperate/derivation shape reduction. -/
theorem temperateDerivationShapeReduction
    (X : Type u) [Fintype X] [Nonempty X]
    (t : ℝ) (τ : ProbabilityMeasure Param) (σ : FiniteMeasure Param) :
    (∀ ht : 0 < t,
      CMMonotoneAtRow X (HTemp t ht.ne' τ) ↔
        ConcaveCone (columnPhi t τ : ConeVec X → ℝ)) ∧
    (∀ ht : t < 0,
      CMMonotoneAtRow X (HTemp t ht.ne τ) ↔
        ConvexCone (columnPhi t τ : ConeVec X → ℝ)) ∧
    (CMMonotoneAtRow X (HZero σ) ↔
      ConcaveCone (columnDeriv σ : ConeVec X → ℝ)) := by
  constructor
  · intro ht
    exact ⟨concave_columnPhi_of_cmMonotoneAtRow X t ht τ,
      cmMonotoneAtRow_HTemp_of_concave X t ht τ⟩
  constructor
  · intro ht
    exact ⟨convex_columnPhi_of_cmMonotoneAtRow X t ht τ,
      cmMonotoneAtRow_HTemp_of_convex X t ht τ⟩
  · exact ⟨concave_columnDeriv_of_cmMonotoneAtRow X σ,
      cmMonotoneAtRow_HZero_of_concave X σ⟩

/-- Global temperate/derivation shape reduction, obtained by commuting the
universal row alphabet with the fixed-row equivalences. -/
theorem globalTemperateDerivationShapeReduction
    (t : ℝ) (τ : ProbabilityMeasure Param) (σ : FiniteMeasure Param) :
    (∀ ht : 0 < t,
      CMMonotone (HTemp t ht.ne' τ : PolyJointFunctional.{u}) ↔
        ∀ {X : Type u} [Fintype X] [Nonempty X],
          ConcaveCone (columnPhi t τ : ConeVec X → ℝ)) ∧
    (∀ ht : t < 0,
      CMMonotone (HTemp t ht.ne τ : PolyJointFunctional.{u}) ↔
        ∀ {X : Type u} [Fintype X] [Nonempty X],
          ConvexCone (columnPhi t τ : ConeVec X → ℝ)) ∧
    (CMMonotone (HZero σ : PolyJointFunctional.{u}) ↔
      ∀ {X : Type u} [Fintype X] [Nonempty X],
        ConcaveCone (columnDeriv σ : ConeVec X → ℝ)) := by
  constructor
  · intro ht
    constructor
    · intro hmono X _ _
      apply concave_columnPhi_of_cmMonotoneAtRow X t ht τ
      intro Y Y' _ _ _ _ P Q hPQ
      exact hmono P Q hPQ
    · intro hshape X Y Y' _ _ _ _ _ _ P Q hPQ
      exact cmMonotoneAtRow_HTemp_of_concave X t ht τ hshape P Q hPQ
  constructor
  · intro ht
    constructor
    · intro hmono X _ _
      apply convex_columnPhi_of_cmMonotoneAtRow X t ht τ
      intro Y Y' _ _ _ _ P Q hPQ
      exact hmono P Q hPQ
    · intro hshape X Y Y' _ _ _ _ _ _ P Q hPQ
      exact cmMonotoneAtRow_HTemp_of_convex X t ht τ hshape P Q hPQ
  · constructor
    · intro hmono X _ _
      apply concave_columnDeriv_of_cmMonotoneAtRow X σ
      intro Y Y' _ _ _ _ P Q hPQ
      exact hmono P Q hPQ
    · intro hshape X Y Y' _ _ _ _ _ _ P Q hPQ
      exact cmMonotoneAtRow_HZero_of_concave X σ hshape P Q hPQ

end ConditionalEntropy
