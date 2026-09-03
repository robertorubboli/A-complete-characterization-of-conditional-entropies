import ConditionalEntropy.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Conditioning maps and one-column shape

This module defines the one-column lift used throughout the development. A
positively homogeneous one-column functional is summed over conditioning
columns, and concavity or convexity controls its behavior under row-stochastic
maps on the conditioning register.
-/

open scoped BigOperators

namespace ConditionalEntropy

/-- A finite row-stochastic matrix. -/
structure RowStochastic (ι κ : Type*) [Fintype κ] where
  toFun : ι → κ → ℝ
  nonneg : ∀ i k, 0 ≤ toFun i k
  sum_row : ∀ i, ∑ k, toFun i k = 1

instance {ι κ : Type*} [Fintype κ] : CoeFun (RowStochastic ι κ) (fun _ => ι → κ → ℝ) :=
  ⟨RowStochastic.toFun⟩

/-- Positive homogeneity on nonnegative scalars. -/
def IsPosHomogeneous {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : E → ℝ) : Prop :=
  ∀ c : ℝ, 0 ≤ c → ∀ x, f (c • x) = c * f x

/-- Superadditivity, the finite-sum form of concavity plus positive homogeneity. -/
def IsSuperadditive {E : Type*} [Add E] (f : E → ℝ) : Prop :=
  ∀ x z, f x + f z ≤ f (x + z)

/-- Subadditivity, the finite-sum form of convexity plus positive homogeneity. -/
def IsSubadditive {E : Type*} [Add E] (f : E → ℝ) : Prop :=
  ∀ x z, f (x + z) ≤ f x + f z

/-- The lift of a one-column functional to a finite conditioning register. -/
noncomputable def columnLift {E ι : Type*} [Fintype ι] (f : E → ℝ) (P : ι → E) : ℝ :=
  ∑ i, f (P i)

/-- Action of a row-stochastic map on a finite family of columns. -/
noncomputable def pushConditioning {E ι κ : Type*} [AddCommMonoid E] [Module ℝ E]
    [Fintype ι] [Fintype κ] (P : ι → E) (D : RowStochastic ι κ) : κ → E :=
  fun k => ∑ i, D i k • P i

theorem isSuperadditive_of_concave_posHomogeneous
    {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : E → ℝ)
    (hconc : IsConcave f) (hhom : IsPosHomogeneous f) : IsSuperadditive f := by
  intro x z
  have hx := hhom (2 : ℝ) (by norm_num) x
  have hz := hhom (2 : ℝ) (by norm_num) z
  have h := hconc ((2 : ℝ) • x) ((2 : ℝ) • z) (1 / 2 : ℝ)
    (by norm_num) (by norm_num)
  rw [hx, hz] at h
  have hcoeff : (1 / 2 : ℝ) * (2 * f x) + (1 - 1 / 2) * (2 * f z) =
      f x + f z := by ring
  have harg : (1 / 2 : ℝ) • ((2 : ℝ) • x) +
      (1 - 1 / 2 : ℝ) • ((2 : ℝ) • z) = x + z := by module
  rw [hcoeff, harg] at h
  exact h

theorem isSubadditive_of_convex_posHomogeneous
    {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : E → ℝ)
    (hconv : IsConvex f) (hhom : IsPosHomogeneous f) : IsSubadditive f := by
  intro x z
  have hx := hhom (2 : ℝ) (by norm_num) x
  have hz := hhom (2 : ℝ) (by norm_num) z
  have h := hconv ((2 : ℝ) • x) ((2 : ℝ) • z) (1 / 2 : ℝ)
    (by norm_num) (by norm_num)
  rw [hx, hz] at h
  have hcoeff : (1 / 2 : ℝ) * (2 * f x) + (1 - 1 / 2) * (2 * f z) =
      f x + f z := by ring
  have harg : (1 / 2 : ℝ) • ((2 : ℝ) • x) +
      (1 - 1 / 2 : ℝ) • ((2 : ℝ) • z) = x + z := by module
  rw [hcoeff, harg] at h
  exact h

theorem superadditive_finset_sum
    {E ι : Type*} [AddCommMonoid E] (f : E → ℝ) (hadd : IsSuperadditive f)
    (hzero : f 0 = 0) (s : Finset ι) (v : ι → E) :
    ∑ i ∈ s, f (v i) ≤ f (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact le_trans (add_le_add (le_refl _) ih) (hadd _ _)

theorem subadditive_finset_sum
    {E ι : Type*} [AddCommMonoid E] (f : E → ℝ) (hadd : IsSubadditive f)
    (hzero : f 0 = 0) (s : Finset ι) (v : ι → E) :
    f (∑ i ∈ s, v i) ≤ ∑ i ∈ s, f (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact le_trans (hadd _ _) (add_le_add (le_refl _) ih)

theorem columnLift_pushConditioning_ge
    {E ι κ : Type*} [AddCommMonoid E] [Module ℝ E] [Fintype ι] [Fintype κ]
    (f : E → ℝ) (hadd : IsSuperadditive f) (hhom : IsPosHomogeneous f)
    (P : ι → E) (D : RowStochastic ι κ) :
    columnLift f P ≤ columnLift f (pushConditioning P D) := by
  classical
  have hzero : f 0 = 0 := by
    have h := hhom 0 (le_refl 0) 0
    simpa using h
  calc
    columnLift f P = ∑ k, ∑ i, D i k * f (P i) := by
      simp only [columnLift]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, D.sum_row, one_mul]
    _ = ∑ k, ∑ i, f (D i k • P i) := by
      congr 1
      funext k
      apply Finset.sum_congr rfl
      intro i _
      rw [hhom (D i k) (D.nonneg i k) (P i)]
    _ ≤ ∑ k, f (∑ i, D i k • P i) := by
      gcongr with k
      simpa using superadditive_finset_sum f hadd hzero Finset.univ
        (fun i => D i k • P i)
    _ = columnLift f (pushConditioning P D) := rfl

theorem columnLift_pushConditioning_le
    {E ι κ : Type*} [AddCommMonoid E] [Module ℝ E] [Fintype ι] [Fintype κ]
    (f : E → ℝ) (hadd : IsSubadditive f) (hhom : IsPosHomogeneous f)
    (P : ι → E) (D : RowStochastic ι κ) :
    columnLift f (pushConditioning P D) ≤ columnLift f P := by
  classical
  have hzero : f 0 = 0 := by
    have h := hhom 0 (le_refl 0) 0
    simpa using h
  calc
    columnLift f (pushConditioning P D) = ∑ k, f (∑ i, D i k • P i) := rfl
    _ ≤ ∑ k, ∑ i, f (D i k • P i) := by
      gcongr with k
      simpa using subadditive_finset_sum f hadd hzero Finset.univ
        (fun i => D i k • P i)
    _ = ∑ k, ∑ i, D i k * f (P i) := by
      congr 1
      funext k
      apply Finset.sum_congr rfl
      intro i _
      rw [hhom (D i k) (D.nonneg i k) (P i)]
    _ = columnLift f P := by
      simp only [columnLift]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, D.sum_row, one_mul]

/-- Concavity implies monotonicity after lifting to conditioning columns. -/
theorem conditioning_monotone_of_concave
    {E ι κ : Type*} [AddCommMonoid E] [Module ℝ E] [Fintype ι] [Fintype κ]
    (f : E → ℝ) (hconc : IsConcave f) (hhom : IsPosHomogeneous f)
    (P : ι → E) (D : RowStochastic ι κ) :
    columnLift f P ≤ columnLift f (pushConditioning P D) :=
  columnLift_pushConditioning_ge f
    (isSuperadditive_of_concave_posHomogeneous f hconc hhom) hhom P D

/-- Convexity gives the reverse order used by the negative-temperate branch. -/
theorem conditioning_antitone_of_convex
    {E ι κ : Type*} [AddCommMonoid E] [Module ℝ E] [Fintype ι] [Fintype κ]
    (f : E → ℝ) (hconv : IsConvex f) (hhom : IsPosHomogeneous f)
    (P : ι → E) (D : RowStochastic ι κ) :
    columnLift f (pushConditioning P D) ≤ columnLift f P :=
  columnLift_pushConditioning_le f
    (isSubadditive_of_convex_posHomogeneous f hconv hhom) hhom P D

end ConditionalEntropy
