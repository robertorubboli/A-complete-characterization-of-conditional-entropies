import ConditionalEntropy.Perspective
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Curvature closure operations

Positive integration and finite pointwise limits preserve the custom cone
curvature predicates used by the classification.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace ConditionalEntropy

universe u

def integrateConeFamily {I : Type u} [Fintype I]
    (ν : Measure Param) (F : Param → ConeVec I → ℝ) : ConeVec I → ℝ :=
  fun x => ∫ a, F a x ∂ν

/-- Positive integration preserves concavity and convexity pointwise. -/
theorem integrationCurvature {I : Type u} [Fintype I] [Nonempty I]
    (ν : Measure Param) [IsFiniteMeasure ν]
    (F : Param → ConeVec I → ℝ)
    (hF : ∀ x : ConeVec I,
      Measurable (fun a => F a x) ∧ Integrable (fun a => F a x) ν) :
    ((∀ᵐ a ∂ν, ConcaveCone (F a)) →
      ConcaveCone (integrateConeFamily ν F)) ∧
    ((∀ᵐ a ∂ν, ConvexCone (F a)) →
      ConvexCone (integrateConeFamily ν F)) := by
  constructor
  · intro hconc x z lambda hlambda
    have hleft : Integrable
        (fun a => lambda * F a x + (1 - lambda) * F a z) ν :=
      ((hF x).2.const_mul lambda).add ((hF z).2.const_mul (1 - lambda))
    have hright : Integrable (fun a => F a (coneMix lambda hlambda x z)) ν :=
      (hF _).2
    change lambda * (∫ a, F a x ∂ν) +
        (1 - lambda) * (∫ a, F a z ∂ν) ≤
      ∫ a, F a (coneMix lambda hlambda x z) ∂ν
    calc
      lambda * (∫ a, F a x ∂ν) + (1 - lambda) * (∫ a, F a z ∂ν) =
          ∫ a, (lambda * F a x + (1 - lambda) * F a z) ∂ν := by
        rw [integral_add ((hF x).2.const_mul lambda)
          ((hF z).2.const_mul (1 - lambda)), integral_const_mul,
          integral_const_mul]
      _ ≤ ∫ a, F a (coneMix lambda hlambda x z) ∂ν :=
        integral_mono_ae hleft hright
          (hconc.mono fun a ha => ha x z lambda hlambda)
  · intro hconv x z lambda hlambda
    have hleft : Integrable (fun a => F a (coneMix lambda hlambda x z)) ν :=
      (hF _).2
    have hright : Integrable
        (fun a => lambda * F a x + (1 - lambda) * F a z) ν :=
      ((hF x).2.const_mul lambda).add ((hF z).2.const_mul (1 - lambda))
    change (∫ a, F a (coneMix lambda hlambda x z) ∂ν) ≤
      lambda * (∫ a, F a x ∂ν) +
        (1 - lambda) * (∫ a, F a z ∂ν)
    calc
      (∫ a, F a (coneMix lambda hlambda x z) ∂ν) ≤
          ∫ a, (lambda * F a x + (1 - lambda) * F a z) ∂ν :=
        integral_mono_ae hleft hright
          (hconv.mono fun a ha => ha x z lambda hlambda)
      _ = lambda * (∫ a, F a x ∂ν) +
          (1 - lambda) * (∫ a, F a z ∂ν) := by
        rw [integral_add ((hF x).2.const_mul lambda)
          ((hF z).2.const_mul (1 - lambda)), integral_const_mul,
          integral_const_mul]

/-- Finite pointwise limits preserve both custom cone curvature predicates. -/
theorem pointwiseCurvatureLimit {I : Type u} [Finite I] [Nonempty I]
    (Fn : ℕ → ConeVec I → ℝ) (F : ConeVec I → ℝ)
    (hlim : ∀ x : ConeVec I, Tendsto (fun n => Fn n x) atTop (𝓝 (F x))) :
    ((∀ n, ConcaveCone (Fn n)) → ConcaveCone F) ∧
    ((∀ n, ConvexCone (Fn n)) → ConvexCone F) := by
  constructor
  · intro hconc x z lambda hlambda
    apply le_of_tendsto_of_tendsto'
      ((tendsto_const_nhds.mul (hlim x)).add
        (tendsto_const_nhds.mul (hlim z)))
      (hlim (coneMix lambda hlambda x z))
    intro n
    exact hconc n x z lambda hlambda
  · intro hconv x z lambda hlambda
    apply le_of_tendsto_of_tendsto'
      (hlim (coneMix lambda hlambda x z))
      ((tendsto_const_nhds.mul (hlim x)).add
        (tendsto_const_nhds.mul (hlim z)))
    intro n
    exact hconv n x z lambda hlambda

end ConditionalEntropy
