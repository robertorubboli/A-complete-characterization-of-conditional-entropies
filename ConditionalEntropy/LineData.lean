import ConditionalEntropy.Renyi
import ConditionalEntropy.ParamMeasure
import Mathlib.Analysis.Convex.Function

/-!
# Positive multiplicative lines and escort statistics

These total, proof-carrying definitions are the common input to signed
differentiation and all block-localization constructions.
-/

noncomputable section

open Set
open scoped BigOperators ENNReal NNReal

namespace ConditionalEntropy

universe u

/-- Strictly positive base data with a multiplicative velocity. -/
structure PositiveLineData (I : Type u) where
  x : I → ℝ
  u : I → ℝ
  x_pos : ∀ i, 0 < x i

/-- Raw affine multiplicative line. -/
def lineRaw {I : Type u} (L : PositiveLineData I) (lambda : ℝ) (i : I) : ℝ :=
  L.x i * (1 + L.u i * lambda)

/-- Coordinatewise strict positivity of a line at one parameter. -/
def LinePositive {I : Type u} (L : PositiveLineData I) (lambda : ℝ) : Prop :=
  ∀ i, 0 < lineRaw L lambda i

theorem linePositiveZero {I : Type u} (L : PositiveLineData I) :
    LinePositive L 0 := by
  intro i
  simpa [lineRaw] using L.x_pos i

/-- Bundle a positive line point in the nonnegative cone. -/
def lineCone {I : Type u} (L : PositiveLineData I) (lambda : ℝ)
    (h : LinePositive L lambda) : ConeVec I :=
  ⟨lineRaw L lambda, fun i => (h i).le⟩

/-- Bundle a positive line point in the punctured cone. -/
def linePosCone {I : Type u} [Nonempty I]
    (L : PositiveLineData I) (lambda : ℝ)
    (h : LinePositive L lambda) : PosConeVec I :=
  ⟨lineCone L lambda h, by
    intro hz
    let i₀ : I := Classical.choice inferInstance
    have hi : lineRaw L lambda i₀ = 0 := by
      exact congrFun hz i₀
    exact (h i₀).ne' hi⟩

/-- Total cone wrapper, equal to zero outside the positive domain. -/
noncomputable def lineConeTotal {I : Type u}
    (L : PositiveLineData I) (lambda : ℝ) : ConeVec I := by
  classical
  exact if h : LinePositive L lambda then lineCone L lambda h else 0

/-- Total punctured-cone wrapper, falling back to the positive base point. -/
noncomputable def linePosConeTotal {I : Type u} [Nonempty I]
    (L : PositiveLineData I) (lambda : ℝ) : PosConeVec I := by
  classical
  exact if h : LinePositive L lambda then linePosCone L lambda h
    else linePosCone L 0 (linePositiveZero L)

/-- Total normalized probability line. -/
noncomputable def lineProb {I : Type u} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) (lambda : ℝ) : ProbVec I := by
  classical
  exact if h : LinePositive L lambda then normalize (linePosCone L lambda h)
    else uniformProb

@[simp] theorem lineConeTotal_of_positive {I : Type u}
    (L : PositiveLineData I) (lambda : ℝ) (h : LinePositive L lambda) :
    lineConeTotal L lambda = lineCone L lambda h := by
  simp [lineConeTotal, h]

@[simp] theorem linePosConeTotal_of_positive {I : Type u} [Nonempty I]
    (L : PositiveLineData I) (lambda : ℝ) (h : LinePositive L lambda) :
    linePosConeTotal L lambda = linePosCone L lambda h := by
  simp [linePosConeTotal, h]

@[simp] theorem lineProb_of_positive {I : Type u} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) (lambda : ℝ) (h : LinePositive L lambda) :
    lineProb L lambda = normalize (linePosCone L lambda h) := by
  simp [lineProb, h]

/-- A raw line is affine in its scalar parameter. -/
theorem lineRaw_affine {I : Type u} (L : PositiveLineData I)
    (a b s : ℝ) (i : I) :
    lineRaw L (s * a + (1 - s) * b) i =
      s * lineRaw L a i + (1 - s) * lineRaw L b i := by
  simp only [lineRaw]
  ring

/-- The proof-carrying cone line respects affine interpolation. -/
theorem lineCone_mix {I : Type u} (L : PositiveLineData I)
    (a b lambda : ℝ) (hlambda : lambda ∈ Icc (0 : ℝ) 1)
    (ha : LinePositive L a) (hb : LinePositive L b)
    (hw : LinePositive L (lambda * a + (1 - lambda) * b)) :
    coneMix lambda hlambda (lineCone L a ha) (lineCone L b hb) =
      lineCone L (lambda * a + (1 - lambda) * b) hw := by
  apply Subtype.ext
  funext i
  exact (lineRaw_affine L a b lambda i).symm

/-- Restriction of cone concavity or convexity to a positive affine line. -/
theorem coneAffineLineBridge {I : Type u} [Nonempty I]
    (L : PositiveLineData I) (U : Set ℝ) (hUconvex : Convex ℝ U)
    (hUpos : ∀ lambda ∈ U, LinePositive L lambda)
    (F : ConeVec I → ℝ) :
    (ConcaveCone F →
      ConcaveOn ℝ U (fun lambda => F (lineConeTotal L lambda))) ∧
    (ConvexCone F →
      ConvexOn ℝ U (fun lambda => F (lineConeTotal L lambda))) := by
  constructor
  · intro hconc
    refine ⟨hUconvex, ?_⟩
    intro a ha b hb lambda mu hlambda hmu hsum
    have hmuEq : mu = 1 - lambda := by linarith
    subst mu
    have hla := hUpos a ha
    have hlb := hUpos b hb
    have hmixmem : lambda * a + (1 - lambda) * b ∈ U := by
      simpa [smul_eq_mul] using
        hUconvex ha hb hlambda (sub_nonneg.mpr (by linarith)) (by linarith)
    have hlmix := hUpos _ hmixmem
    have hc := hconc (lineCone L a hla) (lineCone L b hlb) lambda
      ⟨hlambda, by linarith⟩
    rw [lineCone_mix L a b lambda ⟨hlambda, by linarith⟩ hla hlb hlmix] at hc
    simpa [lineConeTotal_of_positive, hla, hlb, hlmix, smul_eq_mul] using hc
  · intro hconv
    refine ⟨hUconvex, ?_⟩
    intro a ha b hb lambda mu hlambda hmu hsum
    have hmuEq : mu = 1 - lambda := by linarith
    subst mu
    have hla := hUpos a ha
    have hlb := hUpos b hb
    have hmixmem : lambda * a + (1 - lambda) * b ∈ U := by
      simpa [smul_eq_mul] using
        hUconvex ha hb hlambda (sub_nonneg.mpr (by linarith)) (by linarith)
    have hlmix := hUpos _ hmixmem
    have hc := hconv (lineCone L a hla) (lineCone L b hlb) lambda
      ⟨hlambda, by linarith⟩
    rw [lineCone_mix L a b lambda ⟨hlambda, by linarith⟩ hla hlb hlmix] at hc
    simpa [lineConeTotal_of_positive, hla, hlb, hlmix, smul_eq_mul] using hc

/-- Scalar quasi-convexity on a subset of the real line. -/
def ScalarQCvxOn (U : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ a ∈ U, ∀ b ∈ U, ∀ lambda : ℝ,
    0 ≤ lambda → lambda ≤ 1 →
    lambda * a + (1 - lambda) * b ∈ U →
    g (lambda * a + (1 - lambda) * b) ≤ max (g a) (g b)

/-- Quasi-convexity on the punctured cone. -/
def QCvx {I : Type u} (g : PosConeVec I → ℝ) : Prop :=
  ∀ x z : PosConeVec I, ∀ lambda : ℝ,
    ∀ hlambda : 0 < lambda ∧ lambda < 1,
      g (posMix lambda hlambda x z) ≤ max (g x) (g z)

/-- Entropy evaluated along a total normalized line. -/
def entropyLine {I : Type u} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) (a : Param) (lambda : ℝ) : ℝ :=
  renyi a (lineProb L lambda)

/-- First derivative of an entropy line. -/
def entropyLineFirst {I : Type u} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) (a : Param) (lambda : ℝ) : ℝ :=
  deriv (entropyLine L a) lambda

/-- Second derivative of an entropy line. -/
def entropyLineSecond {I : Type u} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) (a : Param) (lambda : ℝ) : ℝ :=
  secondDeriv (entropyLine L a) lambda

/-- Escort probability weight of one coordinate. -/
def escortWeight {I : Type u} [Fintype I]
    (L : PositiveLineData I) (a lambda : ℝ) (i : I) : ℝ :=
  lineRaw L lambda i ^ a / ∑ j, lineRaw L lambda j ^ a

/-- Effective logarithmic line velocity. -/
def effectiveVelocity {I : Type u}
    (L : PositiveLineData I) (lambda : ℝ) (i : I) : ℝ :=
  L.u i / (1 + L.u i * lambda)

/-- Escort mean of effective velocities. -/
def escortMean {I : Type u} [Fintype I]
    (L : PositiveLineData I) (a lambda : ℝ) : ℝ :=
  ∑ i, escortWeight L a lambda i * effectiveVelocity L lambda i

/-- Escort second moment. -/
def escortSecond {I : Type u} [Fintype I]
    (L : PositiveLineData I) (a lambda : ℝ) : ℝ :=
  ∑ i, escortWeight L a lambda i * (effectiveVelocity L lambda i) ^ 2

/-- Escort variance. -/
def escortVar {I : Type u} [Fintype I]
    (L : PositiveLineData I) (a lambda : ℝ) : ℝ :=
  escortSecond L a lambda - (escortMean L a lambda) ^ 2

/-- One coordinate remains maximal, and ties have the same velocity. -/
def FixedMaxCoordinate {I : Type u}
    (L : PositiveLineData I) (U : Set ℝ) (istar : I) : Prop :=
  ∀ lambda ∈ U,
    LinePositive L lambda ∧
      (∀ i, lineRaw L lambda i ≤ lineRaw L lambda istar) ∧
      (∀ i, lineRaw L lambda i = lineRaw L lambda istar →
        effectiveVelocity L lambda i = effectiveVelocity L lambda istar)

/-- Shannon-line slope in the escort notation. -/
def shannonLineSlope {I : Type u} [Fintype I] [Nonempty I]
    (L : PositiveLineData I) (lambda : ℝ) : ℝ :=
  -∑ i, (lineProb L lambda).1 i *
    (effectiveVelocity L lambda i - escortMean L 1 lambda) *
      Real.log ((lineProb L lambda).1 i)

end ConditionalEntropy
