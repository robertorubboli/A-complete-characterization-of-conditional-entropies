import ConditionalEntropy.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Pointwise limits preserve shape

This file supplies the pointwise-limit closure results packaged by Lemma A.7
of the complete-proof document. The proof uses only closure of the order
relation on `ℝ` and continuity of addition, multiplication, and `max`.
-/

open Filter
open scoped Topology

namespace ConditionalEntropy

/-- A pointwise limit of concave real-valued functions is concave. -/
theorem isConcave_of_pointwise_tendsto
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f : ℕ → E → ℝ) (g : E → ℝ)
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hconc : ∀ n, IsConcave (f n)) : IsConcave g := by
  intro x z t ht0 ht1
  refine le_of_tendsto_of_tendsto' ?_ (hlim _) (fun n => hconc n x z t ht0 ht1)
  exact (tendsto_const_nhds.mul (hlim x)).add
    (tendsto_const_nhds.mul (hlim z))

/-- A pointwise limit of convex real-valued functions is convex. -/
theorem isConvex_of_pointwise_tendsto
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f : ℕ → E → ℝ) (g : E → ℝ)
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hconv : ∀ n, IsConvex (f n)) : IsConvex g := by
  intro x z t ht0 ht1
  refine le_of_tendsto_of_tendsto' (hlim _) ?_ (fun n => hconv n x z t ht0 ht1)
  exact (tendsto_const_nhds.mul (hlim x)).add
    (tendsto_const_nhds.mul (hlim z))

/-- A pointwise limit of quasi-convex real-valued functions is quasi-convex. -/
theorem isQuasiConvex_of_pointwise_tendsto
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f : ℕ → E → ℝ) (g : E → ℝ)
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hquasi : ∀ n, IsQuasiConvex (f n)) : IsQuasiConvex g := by
  intro x z t ht0 ht1
  refine le_of_tendsto_of_tendsto' (hlim _) ((hlim x).max (hlim z))
    (fun n => hquasi n x z t ht0 ht1)

/-- The analogous closure statement for strong quasi-concavity. -/
theorem isStronglyQuasiConcave_of_pointwise_tendsto
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f : ℕ → E → ℝ) (g : E → ℝ)
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hquasi : ∀ n, IsStronglyQuasiConcave (f n)) : IsStronglyQuasiConcave g := by
  intro x z t ht0 ht1
  refine le_of_tendsto_of_tendsto' ((hlim x).max (hlim z)) (hlim _)
    (fun n => hquasi n x z t ht0 ht1)

end ConditionalEntropy
