import ConditionalEntropy.CompactUniform

/-!
# Bridge from explicit compact errors to Mathlib uniform convergence

The localization layer records convergence through an explicit supremum
error.  Stationarity correction uses Mathlib's `TendstoUniformlyOn`; this
module proves the direct implication once and for all.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace ConditionalEntropy

universe u

/-- Vanishing explicit compact-uniform error implies uniform convergence on
the same compact set. -/
theorem compactUniformConverges_tendstoUniformlyOn
    {U : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U]
    (K : Set U) (_hK0 : K.Nonempty) (hK : IsCompact K)
    (fN : ℕ → U → ℝ) (f : U → ℝ)
    (hfN : ∀ n, ContinuousOn (fN n) K) (hf : ContinuousOn f K)
    (hconv : CompactUniformConverges K fN f) :
    TendstoUniformlyOn fN f atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hevent : ∀ᶠ n in atTop,
      compactUniformError K fN f n < epsilon :=
    hconv.eventually (Iio_mem_nhds hepsilon)
  filter_upwards [hevent] with n hn
  intro x hx
  rw [Real.dist_eq, abs_sub_comm]
  exact (compactUniformError_point_le K hK fN f n
    (hfN n) hf hx).trans_lt hn

end ConditionalEntropy
