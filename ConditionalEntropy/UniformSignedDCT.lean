import ConditionalEntropy.CompactUniform
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Uniform dominated convergence

This file proves the two uniform dominated-convergence packages used by the
localization arguments.  The signed version is reduced to the positive one at
the level of estimates through the canonical Jordan decomposition and its
total-variation measure.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace ConditionalEntropy

universe u v

private theorem signedIntegral_sub_of_integrable
    {E : Type u} [MeasurableSpace E] (mu : SignedMeasure E)
    {f g : E → ℝ}
    (hfPos : Integrable f (signedPos mu))
    (hfNeg : Integrable f (signedNeg mu))
    (hgPos : Integrable g (signedPos mu))
    (hgNeg : Integrable g (signedNeg mu)) :
    signedIntegral mu (fun e => f e - g e) =
      signedIntegral mu f - signedIntegral mu g := by
  unfold signedIntegral
  rw [integral_sub hfPos hgPos, integral_sub hfNeg hgNeg]
  ring

/-- Absolute value of the Jordan signed integral is bounded by the integral
of the absolute value against total variation. -/
private theorem abs_signedIntegral_le_integral_abs
    {E : Type u} [MeasurableSpace E] (mu : SignedMeasure E)
    {f : E → ℝ}
    (hfPos : Integrable f (signedPos mu))
    (hfNeg : Integrable f (signedNeg mu)) :
    |signedIntegral mu f| ≤ ∫ e, |f e| ∂signedTV mu := by
  rw [signedTV_eq_add, integral_add_measure hfPos.abs hfNeg.abs]
  unfold signedIntegral
  calc
    |(∫ e, f e ∂signedPos mu) - ∫ e, f e ∂signedNeg mu| ≤
        |(∫ e, f e ∂signedPos mu)| +
          |(∫ e, f e ∂signedNeg mu)| := abs_sub _ _
    _ ≤ (∫ e, |f e| ∂signedPos mu) +
          ∫ e, |f e| ∂signedNeg mu := by
      exact add_le_add
        (by simpa [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := signedPos mu) f))
        (by simpa [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (μ := signedNeg mu) f))

private theorem pointError_integrable
    {E : Type u} [MeasurableSpace E] {K : Type v}
    (nu : Measure E) (fN : ℕ → E → K → ℝ) (f : E → K → ℝ)
    (G : E → ℝ)
    (hMeas : ∀ n, Measurable (uniformPointError fN f n))
    (hG : Integrable G nu)
    (hDom : ∀ n e, 0 ≤ uniformPointError fN f n e ∧
      uniformPointError fN f n e ≤ G e) (n : ℕ) :
    Integrable (uniformPointError fN f n) nu := by
  apply hG.mono' (hMeas n).aestronglyMeasurable
  filter_upwards [] with e
  rw [Real.norm_eq_abs, abs_of_nonneg (hDom n e).1]
  exact (hDom n e).2

private theorem pointError_integral_tendsto_zero
    {E : Type u} [MeasurableSpace E] {K : Type v}
    (nu : Measure E) (fN : ℕ → E → K → ℝ) (f : E → K → ℝ)
    (G : E → ℝ)
    (hMeas : ∀ n, Measurable (uniformPointError fN f n))
    (hConv : ∀ᵐ e ∂nu, Tendsto
      (fun n => uniformPointError fN f n e) atTop (nhds 0))
    (hG : Integrable G nu)
    (hDom : ∀ n e, 0 ≤ uniformPointError fN f n e ∧
      uniformPointError fN f n e ≤ G e) :
    Tendsto (fun n => ∫ e, uniformPointError fN f n e ∂nu)
      atTop (nhds 0) := by
  have hBound : ∀ n, ∀ᵐ e ∂nu,
      ‖uniformPointError fN f n e‖ ≤ G e := by
    intro n
    filter_upwards [] with e
    rw [Real.norm_eq_abs, abs_of_nonneg (hDom n e).1]
    exact (hDom n e).2
  simpa using tendsto_integral_of_dominated_convergence G
    (fun n => (hMeas n).aestronglyMeasurable) hG hBound hConv

private theorem positiveIntegralPointBound
    {E : Type u} [MeasurableSpace E] {K : Type v}
    (nu : Measure E) (fN : ℕ → E → K → ℝ) (f : E → K → ℝ)
    (hFN : ∀ n k, Integrable (fun e => fN n e k) nu)
    (hF : ∀ k, Integrable (fun e => f e k) nu)
    (hBdd : ∀ n e, BddAbove
      {r : ℝ | ∃ k : K, r = |fN n e k - f e k|})
    (hPointInt : ∀ n, Integrable (uniformPointError fN f n) nu)
    (n : ℕ) (k : K) :
    |(∫ e, fN n e k ∂nu) - ∫ e, f e k ∂nu| ≤
      ∫ e, uniformPointError fN f n e ∂nu := by
  have hDiff : Integrable (fun e => fN n e k - f e k) nu :=
    (hFN n k).sub (hF k)
  have hPoint : ∀ e, |fN n e k - f e k| ≤
      uniformPointError fN f n e := by
    intro e
    unfold uniformPointError
    exact le_csSup (hBdd n e) ⟨k, rfl⟩
  calc
    |(∫ e, fN n e k ∂nu) - ∫ e, f e k ∂nu| =
        |∫ e, (fN n e k - f e k) ∂nu| := by
      rw [integral_sub (hFN n k) (hF k)]
    _ ≤ ∫ e, |fN n e k - f e k| ∂nu := by
      simpa [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := nu)
          (fun e => fN n e k - f e k))
    _ ≤ ∫ e, uniformPointError fN f n e ∂nu :=
      integral_mono hDiff.abs (hPointInt n) hPoint

private theorem signedIntegralPointBound
    {E : Type u} [MeasurableSpace E] {K : Type v}
    (mu : SignedMeasure E) (fN : ℕ → E → K → ℝ) (f : E → K → ℝ)
    (hFNPos : ∀ n k, Integrable (fun e => fN n e k) (signedPos mu))
    (hFNNeg : ∀ n k, Integrable (fun e => fN n e k) (signedNeg mu))
    (hFPos : ∀ k, Integrable (fun e => f e k) (signedPos mu))
    (hFNeg : ∀ k, Integrable (fun e => f e k) (signedNeg mu))
    (hBdd : ∀ n e, BddAbove
      {r : ℝ | ∃ k : K, r = |fN n e k - f e k|})
    (hPointInt : ∀ n, Integrable (uniformPointError fN f n) (signedTV mu))
    (n : ℕ) (k : K) :
    |signedIntegral mu (fun e => fN n e k) -
        signedIntegral mu (fun e => f e k)| ≤
      ∫ e, uniformPointError fN f n e ∂signedTV mu := by
  have hDiffPos : Integrable (fun e => fN n e k - f e k) (signedPos mu) :=
    (hFNPos n k).sub (hFPos k)
  have hDiffNeg : Integrable (fun e => fN n e k - f e k) (signedNeg mu) :=
    (hFNNeg n k).sub (hFNeg k)
  have hDiffTV : Integrable (fun e => |fN n e k - f e k|) (signedTV mu) := by
    rw [signedTV_eq_add]
    exact hDiffPos.abs.add_measure hDiffNeg.abs
  have hPoint : ∀ e, |fN n e k - f e k| ≤
      uniformPointError fN f n e := by
    intro e
    unfold uniformPointError
    exact le_csSup (hBdd n e) ⟨k, rfl⟩
  calc
    |signedIntegral mu (fun e => fN n e k) -
        signedIntegral mu (fun e => f e k)| =
        |signedIntegral mu (fun e => fN n e k - f e k)| := by
      rw [signedIntegral_sub_of_integrable mu
        (hFNPos n k) (hFNNeg n k) (hFPos k) (hFNeg k)]
    _ ≤ ∫ e, |fN n e k - f e k| ∂signedTV mu :=
      abs_signedIntegral_le_integral_abs mu hDiffPos hDiffNeg
    _ ≤ ∫ e, uniformPointError fN f n e ∂signedTV mu :=
      integral_mono hDiffTV (hPointInt n) hPoint

/-- Uniform dominated convergence for a positive measure
(`fnd-uniform-dct`). -/
theorem uniformDCT
    {E : Type u} [MeasurableSpace E] {K : Type v} [Nonempty K]
    (nu : Measure E) [IsFiniteMeasure nu]
    (fN : ℕ → E → K → ℝ) (f : E → K → ℝ) (G : E → ℝ)
    (hFN : ∀ n k, Measurable (fun e => fN n e k) ∧
      Integrable (fun e => fN n e k) nu)
    (hF : ∀ k, Measurable (fun e => f e k) ∧
      Integrable (fun e => f e k) nu)
    (hBdd : ∀ n e, BddAbove
      {r : ℝ | ∃ k : K, r = |fN n e k - f e k|})
    (hMeas : ∀ n, Measurable (uniformPointError fN f n))
    (hConv : ∀ᵐ e ∂nu, Tendsto
      (fun n => uniformPointError fN f n e) atTop (nhds 0))
    (hG : Integrable G nu)
    (hDom : ∀ n e, 0 ≤ uniformPointError fN f n e ∧
      uniformPointError fN f n e ≤ G e) :
    (∀ n, 0 ≤ uniformIntegralErrorPos nu fN f n ∧
      uniformIntegralErrorPos nu fN f n ≤
        ∫ e, uniformPointError fN f n e ∂nu) ∧
      Tendsto (fun n => uniformIntegralErrorPos nu fN f n)
        atTop (nhds 0) := by
  have hPointInt : ∀ n, Integrable (uniformPointError fN f n) nu :=
    pointError_integrable nu fN f G hMeas hG hDom
  have hOne : ∀ n k,
      |(∫ e, fN n e k ∂nu) - ∫ e, f e k ∂nu| ≤
        ∫ e, uniformPointError fN f n e ∂nu :=
    positiveIntegralPointBound nu fN f
      (fun n k => (hFN n k).2) (fun k => (hF k).2) hBdd hPointInt
  have hBounds : ∀ n, 0 ≤ uniformIntegralErrorPos nu fN f n ∧
      uniformIntegralErrorPos nu fN f n ≤
        ∫ e, uniformPointError fN f n e ∂nu := by
    intro n
    let S : Set ℝ := {r : ℝ | ∃ k : K,
      r = |(∫ e, fN n e k ∂nu) - ∫ e, f e k ∂nu|}
    have hSNonempty : S.Nonempty := by
      let k : K := Classical.choice inferInstance
      exact ⟨_, k, rfl⟩
    have hSBdd : BddAbove S := by
      refine ⟨∫ e, uniformPointError fN f n e ∂nu, ?_⟩
      rintro r ⟨k, rfl⟩
      exact hOne n k
    change 0 ≤ sSup S ∧ sSup S ≤
      ∫ e, uniformPointError fN f n e ∂nu
    constructor
    · obtain ⟨k⟩ := (inferInstance : Nonempty K)
      exact (abs_nonneg _).trans (le_csSup hSBdd ⟨k, rfl⟩)
    · exact csSup_le hSNonempty fun _ hr => by
        rcases hr with ⟨k, rfl⟩
        exact hOne n k
  refine ⟨hBounds, ?_⟩
  apply squeeze_zero
  · exact fun n => (hBounds n).1
  · exact fun n => (hBounds n).2
  · exact pointError_integral_tendsto_zero nu fN f G hMeas hConv hG hDom

/-- Uniform dominated convergence for a signed measure, through its canonical
Jordan components and total variation (`fnd-uniform-dct-signed`). -/
theorem uniformDCTSigned
    {E : Type u} [MeasurableSpace E] {K : Type v} [Nonempty K]
    (mu : SignedMeasure E)
    (fN : ℕ → E → K → ℝ) (f : E → K → ℝ) (G : E → ℝ)
    (hFN : ∀ n k, Measurable (fun e => fN n e k) ∧
      Integrable (fun e => fN n e k) (signedPos mu) ∧
      Integrable (fun e => fN n e k) (signedNeg mu))
    (hF : ∀ k, Measurable (fun e => f e k) ∧
      Integrable (fun e => f e k) (signedPos mu) ∧
      Integrable (fun e => f e k) (signedNeg mu))
    (hBdd : ∀ n e, BddAbove
      {r : ℝ | ∃ k : K, r = |fN n e k - f e k|})
    (hMeas : ∀ n, Measurable (uniformPointError fN f n))
    (hConv : ∀ᵐ e ∂signedTV mu, Tendsto
      (fun n => uniformPointError fN f n e) atTop (nhds 0))
    (hG : Integrable G (signedTV mu))
    (hDom : ∀ n e, 0 ≤ uniformPointError fN f n e ∧
      uniformPointError fN f n e ≤ G e) :
    (∀ n, 0 ≤ uniformIntegralErrorSigned mu fN f n ∧
      uniformIntegralErrorSigned mu fN f n ≤
        ∫ e, uniformPointError fN f n e ∂signedTV mu) ∧
      Tendsto (fun n => uniformIntegralErrorSigned mu fN f n)
        atTop (nhds 0) := by
  have hPointInt : ∀ n,
      Integrable (uniformPointError fN f n) (signedTV mu) :=
    pointError_integrable (signedTV mu) fN f G hMeas hG hDom
  have hOne : ∀ n k,
      |signedIntegral mu (fun e => fN n e k) -
          signedIntegral mu (fun e => f e k)| ≤
        ∫ e, uniformPointError fN f n e ∂signedTV mu :=
    signedIntegralPointBound mu fN f
      (fun n k => (hFN n k).2.1) (fun n k => (hFN n k).2.2)
      (fun k => (hF k).2.1) (fun k => (hF k).2.2)
      hBdd hPointInt
  have hBounds : ∀ n, 0 ≤ uniformIntegralErrorSigned mu fN f n ∧
      uniformIntegralErrorSigned mu fN f n ≤
        ∫ e, uniformPointError fN f n e ∂signedTV mu := by
    intro n
    let S : Set ℝ := {r : ℝ | ∃ k : K,
      r = |signedIntegral mu (fun e => fN n e k) -
        signedIntegral mu (fun e => f e k)|}
    have hSNonempty : S.Nonempty := by
      let k : K := Classical.choice inferInstance
      exact ⟨_, k, rfl⟩
    have hSBdd : BddAbove S := by
      refine ⟨∫ e, uniformPointError fN f n e ∂signedTV mu, ?_⟩
      rintro r ⟨k, rfl⟩
      exact hOne n k
    change 0 ≤ sSup S ∧ sSup S ≤
      ∫ e, uniformPointError fN f n e ∂signedTV mu
    constructor
    · obtain ⟨k⟩ := (inferInstance : Nonempty K)
      exact (abs_nonneg _).trans (le_csSup hSBdd ⟨k, rfl⟩)
    · exact csSup_le hSNonempty fun _ hr => by
        rcases hr with ⟨k, rfl⟩
        exact hOne n k
  refine ⟨hBounds, ?_⟩
  apply squeeze_zero
  · exact fun n => (hBounds n).1
  · exact fun n => (hBounds n).2
  · exact pointError_integral_tendsto_zero
      (signedTV mu) fN f G hMeas hConv hG hDom

end ConditionalEntropy
