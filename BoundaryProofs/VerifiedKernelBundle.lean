import BoundaryProofs.Curvature
import BoundaryProofs.DominantBlock
import BoundaryProofs.Midpoint
import BoundaryProofs.PointwiseLimits
import BoundaryProofs.Stationarity

/-!
# Closed bundle of independently checked boundary kernels

This file packages the public results in `BoundaryProofs` into one closed
proposition.  Each component retains all of its local data and premises under
universal quantifiers; the bundle therefore records exactly the verified
algebraic, order-theoretic, and limit-preservation implications without
asserting a classification theorem.
-/

open scoped BigOperators

namespace ConditionalEntropy

/--
An argument-free conjunction of the independently checked boundary kernels.

The conjuncts follow the module order: curvature and scalar obstructions,
stationarity correction, finite midpoint witnesses, dominant-block estimates,
and pointwise-limit closure of the four shape predicates.
-/
theorem verifiedKernelBundle :
    (∀ (ι : Type*) [Fintype ι] (β a : ι → ℝ),
      IsAffineFamily β →
        monomialCurvature β a =
          -∑ i, β i * (a i - ∑ j, β j * a j) ^ 2) ∧
    (∀ (ι : Type*) [Fintype ι] (β a : ι → ℝ),
      (∀ i, 0 ≤ β i) → IsAffineFamily β →
        monomialCurvature β a ≤ 0) ∧
    (∀ (ι : Type*) [Fintype ι] (β : ι → ℝ),
      (∀ a, monomialCurvature β a ≤ 0) →
        ∀ k, β k ∈ Set.Icc 0 1) ∧
    (∀ (ι : Type*) [Fintype ι] (β : ι → ℝ) (k : ι),
      β k < 0 → ∃ a, 0 < monomialCurvature β a) ∧
    (∀ A C : ℝ, 0 < A → 0 < C →
      C * (1 / C) + A * (-1 / A) = 0 ∧
        -(C * (1 / C) ^ 2 + A * (-1 / A) ^ 2) < 0) ∧
    (∀ A : ℝ, A < 0 → 0 < A ^ 2 - A) ∧
    (∀ B : ℝ, 1 < B → 0 < B ^ 2 - B) ∧
    (∀ m : ℝ, m ≠ 0 → 0 < m ^ 2) ∧
    (∀ A : ℝ, A < 0 → 0 < -A) ∧
    (∀ (m : ℕ) (c z : Fin m → ℝ) (k : Fin m),
      c k ≠ 0 →
        let z' : Fin m → ℝ :=
          fun j => if j = k then z j - (∑ i, c i * z i) / c k else z j
        ∑ i, c i * z' i = 0) ∧
    (∀ (m : ℕ) (c : ℕ → Fin m → ℝ) (cLimit z : Fin m → ℝ) (k : Fin m),
      (∀ i, Filter.Tendsto (fun d => c d i) Filter.atTop (nhds (cLimit i))) →
      (∑ i, cLimit i * z i = 0) →
      cLimit k ≠ 0 →
        Filter.Tendsto
          (fun d j =>
            if j = k then z j - (∑ i, c d i * z i) / c d k else z j)
          Filter.atTop (nhds z)) ∧
    (∀ (E : Type*) [AddCommMonoid E] [Module ℝ E]
        (f : E → ℝ) (x z : E),
      f ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • z) <
          (1 / 2 : ℝ) * f x + (1 / 2 : ℝ) * f z →
        ¬ IsConcave f) ∧
    (∀ (E : Type*) [AddCommMonoid E] [Module ℝ E]
        (f : E → ℝ) (x z : E),
      (1 / 2 : ℝ) * f x + (1 / 2 : ℝ) * f z <
          f ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • z) →
        ¬ IsConvex f) ∧
    (∀ (E : Type*) [AddCommMonoid E] [Module ℝ E]
        (f : E → ℝ) (x z : E),
      max (f x) (f z) <
          f ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • z) →
        ¬ IsQuasiConvex f) ∧
    (∀ (ι : Type*) [Fintype ι]
        (π u : ι → ℝ) (j : ι) (δ M : ℝ),
      (∀ i, 0 ≤ π i) →
      (∑ i, π i = 1) →
      1 - δ ≤ π j →
      (∀ i, |u i| ≤ M) →
      0 ≤ M →
        |weightedMean π u - u j| ≤ 2 * M * δ) ∧
    (∀ (ι : Type*) [Fintype ι]
        (π u : ι → ℝ) (j : ι) (α δ M : ℝ),
      (∀ i, 0 ≤ π i) →
      (∑ i, π i = 1) →
      1 - δ ≤ π j →
      (∀ i, |u i| ≤ M) →
      0 ≤ α →
      0 ≤ M →
        |(-weightedSecondMoment π u + α * weightedVariance π u) + u j ^ 2| ≤
          2 * M ^ 2 * (1 + 2 * α) * δ) ∧
    (∀ (E : Type*) [AddCommMonoid E] [Module ℝ E]
        (f : ℕ → E → ℝ) (g : E → ℝ),
      (∀ x, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x))) →
      (∀ n, IsConcave (f n)) →
        IsConcave g) ∧
    (∀ (E : Type*) [AddCommMonoid E] [Module ℝ E]
        (f : ℕ → E → ℝ) (g : E → ℝ),
      (∀ x, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x))) →
      (∀ n, IsConvex (f n)) →
        IsConvex g) ∧
    (∀ (E : Type*) [AddCommMonoid E] [Module ℝ E]
        (f : ℕ → E → ℝ) (g : E → ℝ),
      (∀ x, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x))) →
      (∀ n, IsQuasiConvex (f n)) →
        IsQuasiConvex g) ∧
    (∀ (E : Type*) [AddCommMonoid E] [Module ℝ E]
        (f : ℕ → E → ℝ) (g : E → ℝ),
      (∀ x, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x))) →
      (∀ n, IsStronglyQuasiConcave (f n)) →
        IsStronglyQuasiConcave g) := by
  exact ⟨
    @monomialCurvature_eq_neg_variance,
    @monomialCurvature_nonpos_of_nonneg,
    @coefficient_mem_Icc_of_curvature_nonpos,
    @monomialCurvature_pos_of_negative_coefficient,
    @two_positive_stationary_witness,
    @negative_tail_concavity_obstruction,
    @excessive_lower_moment_concavity_obstruction,
    @shannon_atom_concavity_obstruction,
    @positive_tail_derivation_obstruction,
    @stationarityCorrection_dot,
    @stationarityCorrection_tendsto,
    @not_concave_of_strict_midpoint_valley,
    @not_convex_of_strict_midpoint_peak,
    @not_quasiConvex_of_strict_midpoint_peak,
    @dominantBlock_first,
    @dominantBlock_second,
    @isConcave_of_pointwise_tendsto,
    @isConvex_of_pointwise_tendsto,
    @isQuasiConvex_of_pointwise_tendsto,
    @isStronglyQuasiConcave_of_pointwise_tendsto
  ⟩

end ConditionalEntropy
