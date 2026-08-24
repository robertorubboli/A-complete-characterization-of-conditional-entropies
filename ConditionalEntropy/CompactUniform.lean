import ConditionalEntropy.ParamMeasure
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Compact-uniform errors

The localization proofs use explicit real suprema rather than an opaque
uniform-convergence predicate.  This module records those exact definitions
and their elementary closure/evaluation rules.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace ConditionalEntropy

universe u v w

/-- Pointwise error after taking the supremum over a parameter type. -/
def uniformPointError {E : Type u} {K : Type v}
    (fN : ℕ → E → K → ℝ) (f : E → K → ℝ) (n : ℕ) (e : E) : ℝ :=
  sSup {r : ℝ | ∃ k : K, r = |fN n e k - f e k|}

/-- Uniform error between positive-measure integrals. -/
def uniformIntegralErrorPos {E : Type u} [MeasurableSpace E] {K : Type v}
    (nu : Measure E) (fN : ℕ → E → K → ℝ) (f : E → K → ℝ) (n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ k : K,
    r = |(∫ e, fN n e k ∂nu) - ∫ e, f e k ∂nu|}

/-- Uniform error between Jordan signed integrals. -/
def uniformIntegralErrorSigned {E : Type u} [MeasurableSpace E] {K : Type v}
    (mu : SignedMeasure E) (fN : ℕ → E → K → ℝ)
    (f : E → K → ℝ) (n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ k : K,
    r = |signedIntegral mu (fun e => fN n e k) -
      signedIntegral mu (fun e => f e k)|}

/-- Supremum error on a named ambient subset. -/
def compactUniformError {U : Type u} (K : Set U)
    (fN : ℕ → U → ℝ) (f : U → ℝ) (n : ℕ) : ℝ :=
  sSup {z : ℝ | ∃ x ∈ K, z = |fN n x - f x|}

/-- Convergence of the explicit compact-uniform error to zero. -/
def CompactUniformConverges {U : Type u} (K : Set U)
    (fN : ℕ → U → ℝ) (f : U → ℝ) : Prop :=
  Tendsto (fun n => compactUniformError K fN f n) atTop (𝓝 0)

private theorem compactErrorSet_eq_image {U : Type u} (K : Set U)
    (fN : ℕ → U → ℝ) (f : U → ℝ) (n : ℕ) :
    {z : ℝ | ∃ x ∈ K, z = |fN n x - f x|} =
      (fun x => |fN n x - f x|) '' K := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem compactUniformError_bddAbove
    {U : Type u} [TopologicalSpace U] (K : Set U)
    (hK : IsCompact K) (fN : ℕ → U → ℝ) (f : U → ℝ) (n : ℕ)
    (hfN : ContinuousOn (fN n) K) (hf : ContinuousOn f K) :
    BddAbove {z : ℝ | ∃ x ∈ K, z = |fN n x - f x|} := by
  rw [compactErrorSet_eq_image]
  exact hK.bddAbove_image (hfN.sub hf).abs

theorem compactUniformError_nonneg
    {U : Type u} [TopologicalSpace U] (K : Set U)
    (hK0 : K.Nonempty) (hK : IsCompact K)
    (fN : ℕ → U → ℝ) (f : U → ℝ) (n : ℕ)
    (hfN : ContinuousOn (fN n) K) (hf : ContinuousOn f K) :
    0 ≤ compactUniformError K fN f n := by
  obtain ⟨x, hx⟩ := hK0
  have hle : |fN n x - f x| ≤ compactUniformError K fN f n := by
    unfold compactUniformError
    exact le_csSup (compactUniformError_bddAbove K hK fN f n hfN hf)
      ⟨x, hx, rfl⟩
  exact (abs_nonneg _).trans hle

theorem compactUniformError_point_le
    {U : Type u} [TopologicalSpace U] (K : Set U)
    (hK : IsCompact K) (fN : ℕ → U → ℝ) (f : U → ℝ) (n : ℕ)
    (hfN : ContinuousOn (fN n) K) (hf : ContinuousOn f K)
    {x : U} (hx : x ∈ K) :
    |fN n x - f x| ≤ compactUniformError K fN f n := by
  unfold compactUniformError
  exact le_csSup (compactUniformError_bddAbove K hK fN f n hfN hf)
    ⟨x, hx, rfl⟩

/-- Evaluation of compact-uniform convergence at a named member. -/
theorem compactUniformEval
    {U : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U]
    (K : Set U) (hK0 : K.Nonempty) (hK : IsCompact K)
    (fN : ℕ → U → ℝ) (f : U → ℝ)
    (hfN : ∀ n, ContinuousOn (fN n) K) (hf : ContinuousOn f K)
    {x : U} (hx : x ∈ K)
    (hconv : CompactUniformConverges K fN f) :
    Tendsto (fun n => fN n x) atTop (𝓝 (f x)) := by
  unfold CompactUniformConverges at hconv
  rw [Metric.tendsto_atTop] at hconv ⊢
  intro eps heps
  obtain ⟨N, hN⟩ := hconv eps heps
  refine ⟨N, fun n hn => ?_⟩
  have hErrDist := hN n hn
  have hnonneg := compactUniformError_nonneg K hK0 hK fN f n (hfN n) hf
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hErrDist
  rw [Real.dist_eq]
  exact (compactUniformError_point_le K hK fN f n (hfN n) hf hx).trans_lt hErrDist

theorem compactUniformError_add_le
    {U : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U]
    (K : Set U) (hK0 : K.Nonempty) (hK : IsCompact K)
    (f1 f2 : ℕ → U → ℝ) (g1 g2 : U → ℝ) (n : ℕ)
    (hf1 : ContinuousOn (f1 n) K) (hf2 : ContinuousOn (f2 n) K)
    (hg1 : ContinuousOn g1 K) (hg2 : ContinuousOn g2 K) :
    compactUniformError K
        (fun m x => f1 m x + f2 m x) (fun x => g1 x + g2 x) n ≤
      compactUniformError K f1 g1 n + compactUniformError K f2 g2 n := by
  unfold compactUniformError
  apply csSup_le
  · obtain ⟨x, hx⟩ := hK0
    exact ⟨|(f1 n x + f2 n x) - (g1 x + g2 x)|, ⟨x, hx, rfl⟩⟩
  · intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have h1 : |f1 n x - g1 x| ≤
        sSup {z : ℝ | ∃ y ∈ K, z = |f1 n y - g1 y|} :=
      le_csSup (compactUniformError_bddAbove K hK f1 g1 n hf1 hg1)
        ⟨x, hx, rfl⟩
    have h2 : |f2 n x - g2 x| ≤
        sSup {z : ℝ | ∃ y ∈ K, z = |f2 n y - g2 y|} :=
      le_csSup (compactUniformError_bddAbove K hK f2 g2 n hf2 hg2)
        ⟨x, hx, rfl⟩
    calc
      |(f1 n x + f2 n x) - (g1 x + g2 x)| =
          |(f1 n x - g1 x) + (f2 n x - g2 x)| := by ring_nf
      _ ≤ |f1 n x - g1 x| + |f2 n x - g2 x| := abs_add_le _ _
      _ ≤ sSup {z : ℝ | ∃ y ∈ K, z = |f1 n y - g1 y|} +
          sSup {z : ℝ | ∃ y ∈ K, z = |f2 n y - g2 y|} := add_le_add h1 h2

/-- Compact-uniform convergence is closed under addition. -/
theorem compactUniformConverges_add
    {U : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U]
    (K : Set U) (hK0 : K.Nonempty) (hK : IsCompact K)
    (f1 f2 : ℕ → U → ℝ) (g1 g2 : U → ℝ)
    (hf1 : ∀ n, ContinuousOn (f1 n) K)
    (hf2 : ∀ n, ContinuousOn (f2 n) K)
    (hg1 : ContinuousOn g1 K) (hg2 : ContinuousOn g2 K)
    (H1 : CompactUniformConverges K f1 g1)
    (H2 : CompactUniformConverges K f2 g2) :
    CompactUniformConverges K
      (fun n x => f1 n x + f2 n x) (fun x => g1 x + g2 x) := by
  apply squeeze_zero
  · intro n
    exact compactUniformError_nonneg K hK0 hK
      (fun m x => f1 m x + f2 m x) (fun x => g1 x + g2 x) n
      ((hf1 n).add (hf2 n)) (hg1.add hg2)
  · intro n
    exact compactUniformError_add_le K hK0 hK f1 f2 g1 g2 n
      (hf1 n) (hf2 n) hg1 hg2
  · simpa using H1.add H2

theorem compactUniformError_singleton {U : Type u}
    (fN : ℕ → U → ℝ) (f : U → ℝ) (x : U) (n : ℕ) :
    compactUniformError ({x} : Set U) fN f n = |fN n x - f x| := by
  simp [compactUniformError]

/-- Compact-uniform convergence on a singleton is ordinary pointwise
convergence at that point. -/
theorem compactUniformSingleton {U : Type u}
    (fN : ℕ → U → ℝ) (f : U → ℝ) (x : U) :
    (∀ n, compactUniformError ({x} : Set U) fN f n =
      |fN n x - f x|) ∧
    (CompactUniformConverges ({x} : Set U) fN f →
      Tendsto (fun n => fN n x) atTop (𝓝 (f x))) := by
  constructor
  · exact fun n => compactUniformError_singleton fN f x n
  · intro h
    unfold CompactUniformConverges at h
    rw [Metric.tendsto_atTop] at h ⊢
    intro eps heps
    obtain ⟨N, hN⟩ := h eps heps
    refine ⟨N, fun n hn => ?_⟩
    have herr := hN n hn
    rw [compactUniformError_singleton] at herr
    simpa [Real.dist_eq] using herr

/-- The subtype formulation used by the uniform signed DCT has exactly the
same error as the corresponding compact-subset formulation. -/
theorem subtypeUniformErrorBridge
    {E : Type u} [MeasurableSpace E] {U : Type v}
    (mu : SignedMeasure E) (K : Set U)
    (fN : ℕ → E → U → ℝ) (f : E → U → ℝ) (n : ℕ) :
    let UK := {x : U // x ∈ K}
    let FN : ℕ → U → ℝ := fun m x =>
      signedIntegral mu (fun e => fN m e x)
    let F : U → ℝ := fun x => signedIntegral mu (fun e => f e x)
    uniformIntegralErrorSigned mu
      (fun m e (x : UK) => fN m e x.1)
      (fun e (x : UK) => f e x.1) n =
        compactUniformError K FN F n := by
  dsimp only
  unfold uniformIntegralErrorSigned compactUniformError
  congr 1
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

end ConditionalEntropy
