import Mathlib.Analysis.Convex.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Real.Basic

/-!
# Basic finite-dimensional shape predicates

The manuscript reduces monotonicity on the conditioning register to shape
properties of a positively homogeneous one-column function.  The definitions
below isolate the one-dimensional inequalities used in Sections 4 and 5.
-/

open scoped BigOperators

namespace ConditionalEntropy

/-- Concavity of a real-valued function on every chord. -/
def IsConcave {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : E → ℝ) : Prop :=
  ∀ x z : E, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    t * f x + (1 - t) * f z ≤ f (t • x + (1 - t) • z)

/-- Convexity of a real-valued function on every chord. -/
def IsConvex {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : E → ℝ) : Prop :=
  ∀ x z : E, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f (t • x + (1 - t) • z) ≤ t * f x + (1 - t) * f z

/-- Quasi-convexity, the shape condition for the negative tropical branch. -/
def IsQuasiConvex {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : E → ℝ) : Prop :=
  ∀ x z : E, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f (t • x + (1 - t) • z) ≤ max (f x) (f z)

/-- Strong quasi-concavity, the shape condition for the positive tropical branch. -/
def IsStronglyQuasiConcave {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f : E → ℝ) : Prop :=
  ∀ x z : E, ∀ t : ℝ, 0 < t → t < 1 →
    max (f x) (f z) ≤ f (t • x + (1 - t) • z)

/-- A finite coefficient family has total mass one. -/
def IsAffineFamily {ι : Type*} [Fintype ι] (β : ι → ℝ) : Prop :=
  ∑ i, β i = 1

/-- Exactly one coefficient is positive and all other coefficients are nonpositive. -/
def HasUniquePositive {ι : Type*} [Fintype ι] (β : ι → ℝ) : Prop :=
  ∃ k, 0 < β k ∧ ∀ i, i ≠ k → β i ≤ 0

/-- The quadratic form governing the Hessian of an affine monomial. -/
noncomputable def monomialCurvature {ι : Type*} [Fintype ι]
    (β a : ι → ℝ) : ℝ :=
  (∑ i, β i * a i) ^ 2 - ∑ i, β i * (a i) ^ 2

/-- The second derivative of an exponential after logarithmic differentiation. -/
noncomputable def exponentialCurvature {ι : Type*} [Fintype ι]
    (β u : ι → ℝ) : ℝ :=
  monomialCurvature β u

/-- The quadratic form governing the second derivative of a logarithmic
tropical functional. -/
noncomputable def tropicalCurvature {ι : Type*} [Fintype ι]
    (β u : ι → ℝ) : ℝ :=
  -∑ i, β i * (u i) ^ 2

end ConditionalEntropy
