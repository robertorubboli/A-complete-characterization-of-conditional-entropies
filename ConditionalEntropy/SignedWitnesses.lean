import ConditionalEntropy.ColumnFunctions
import ConditionalEntropy.Moments

/-!
# Signed witnesses and signed column functions

This module realizes the manuscript's positive and negative finite-measure
witnesses as genuine finite signed measures.  The column functions use the
canonical Jordan signed integral from `ParamMeasure`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ConditionalEntropy

universe u

/-! ## Signed column functions -/

/-- Exponential perspective built from a finite signed parameter measure. -/
def PhiSigned {I : Type u} [Fintype I] [Nonempty I]
    (mu : SignedMeasure Param) (x : ConeVec I) : ℝ :=
  if hx : x = 0 then 0
  else l1Mass x.1 * Real.exp
    (integratedEntropySigned mu (normalize (toPosCone x hx)))

/-- Integrated entropy on a nonzero cone vector against a signed measure. -/
def GSigned {I : Type u} [Fintype I] [Nonempty I]
    (mu : SignedMeasure Param) (z : PosConeVec I) : ℝ :=
  integratedEntropySigned mu (normalize z)

@[simp] theorem PhiSigned_zero {I : Type u} [Fintype I] [Nonempty I]
    (mu : SignedMeasure Param) : PhiSigned mu (0 : ConeVec I) = 0 := by
  simp [PhiSigned]

theorem PhiSigned_of_ne {I : Type u} [Fintype I] [Nonempty I]
    (mu : SignedMeasure Param) (x : ConeVec I) (hx : x ≠ 0) :
    PhiSigned mu x = l1Mass x.1 * Real.exp
      (integratedEntropySigned mu (normalize (toPosCone x hx))) := by
  simp [PhiSigned, hx]

/-! ## Positive and negative witnesses -/

/-- Regard a finite positive measure as a positive signed witness. -/
def positiveSigned {E : Type*} [MeasurableSpace E]
    (nu : FiniteMeasure E) : SignedMeasure E :=
  signedLift nu

/-- Regard a finite positive measure as a negative signed witness. -/
def negativeSigned {E : Type*} [MeasurableSpace E]
    (nu : FiniteMeasure E) : SignedMeasure E :=
  -signedLift nu

/-- Global concavity predicate for the positive exponential witness. -/
def PosPhiConcave (nu : FiniteMeasure Param) : Prop :=
  ∀ {I : Type u} [Fintype I] [Nonempty I],
    ConcaveCone (PhiSigned (positiveSigned nu) : ConeVec I → ℝ)

/-- Global convexity predicate for the negative exponential witness. -/
def NegPhiConvex (nu : FiniteMeasure Param) : Prop :=
  ∀ {I : Type u} [Fintype I] [Nonempty I],
    ConvexCone (PhiSigned (negativeSigned nu) : ConeVec I → ℝ)

/-- Global quasi-convexity predicate for the negative logarithmic witness. -/
def NegGQuasiconvex (nu : FiniteMeasure Param) : Prop :=
  ∀ {I : Type u} [Fintype I] [Nonempty I],
    QCvx (GSigned (negativeSigned nu) : PosConeVec I → ℝ)

/-! ## Witness measure identities -/

@[simp] theorem signedTV_positiveSigned {E : Type*} [MeasurableSpace E]
    (nu : FiniteMeasure E) :
    signedTV (positiveSigned nu) = (nu : Measure E) := by
  exact signedTV_signedLift nu

@[simp] theorem signedTV_negativeSigned {E : Type*} [MeasurableSpace E]
    (nu : FiniteMeasure E) :
    signedTV (negativeSigned nu) = (nu : Measure E) := by
  rw [negativeSigned, signedTV, SignedMeasure.totalVariation_neg]
  exact signedTV_signedLift nu

theorem positiveSigned_finiteScale (c : ℝ) (hc : 0 ≤ c)
    (nu : FiniteMeasure Param) :
    positiveSigned (finiteScale c hc nu) = c • positiveSigned nu := by
  ext s hs
  simp only [positiveSigned, signedLift]
  rw [_root_.smul_apply, Measure.toSignedMeasure_apply_measurable hs,
    Measure.toSignedMeasure_apply_measurable hs]
  change (ENNReal.ofReal c • (nu : Measure Param)).real s =
    c * (nu : Measure Param).real s
  rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal hc]

theorem negativeSigned_finiteScale (c : ℝ) (hc : 0 ≤ c)
    (nu : FiniteMeasure Param) :
    negativeSigned (finiteScale c hc nu) = (-c) • positiveSigned nu := by
  change -positiveSigned (finiteScale c hc nu) = _
  rw [positiveSigned_finiteScale c hc nu]
  exact (neg_smul c (positiveSigned nu)).symm

@[simp] theorem suppSigned_positiveSigned (nu : FiniteMeasure Param) :
    suppSigned (positiveSigned nu) = suppMeasure (finiteMeasure nu) := by
  simp [suppSigned, suppMeasure, finiteMeasure]

@[simp] theorem suppSigned_negativeSigned (nu : FiniteMeasure Param) :
    suppSigned (negativeSigned nu) = suppMeasure (finiteMeasure nu) := by
  simp [suppSigned, suppMeasure, finiteMeasure]

@[simp] theorem signedTV_negativeSigned_singleton (nu : FiniteMeasure Param)
    (a : Param) :
    signedTV (negativeSigned nu) ({a} : Set Param) =
      finiteMeasure nu ({a} : Set Param) := by
  rw [signedTV_negativeSigned]
  rfl

/-- Literal scaling, total-variation, support, and atom bridge. -/
theorem signedWitnessBridge (nu : FiniteMeasure Param) (c : ℝ) (hc : 0 ≤ c) :
    positiveSigned (finiteScale c hc nu) = c • positiveSigned nu ∧
      negativeSigned (finiteScale c hc nu) = (-c) • positiveSigned nu ∧
      signedTV (positiveSigned nu) = finiteMeasure nu ∧
      signedTV (negativeSigned nu) = finiteMeasure nu ∧
      suppSigned (positiveSigned nu) = suppMeasure (finiteMeasure nu) ∧
      suppSigned (negativeSigned nu) = suppMeasure (finiteMeasure nu) ∧
      ∀ a : Param, signedTV (negativeSigned nu) ({a} : Set Param) =
        finiteMeasure nu ({a} : Set Param) := by
  exact ⟨positiveSigned_finiteScale c hc nu,
    negativeSigned_finiteScale c hc nu,
    signedTV_positiveSigned nu,
    signedTV_negativeSigned nu,
    suppSigned_positiveSigned nu,
    suppSigned_negativeSigned nu,
    signedTV_negativeSigned_singleton nu⟩

/-! ## Scalar bridges to the candidate columns -/

/-- Positive multiplication preserves and reflects quasi-convexity. -/
theorem qcvx_pos_mul_iff {I : Type u} (g : PosConeVec I → ℝ)
    {k : ℝ} (hk : 0 < k) :
    QCvx (fun z => k * g z) ↔ QCvx g := by
  constructor
  · intro h x z lambda hlambda
    have hs := h x z lambda hlambda
    rw [← mul_max_of_nonneg (g x) (g z) hk.le] at hs
    nlinarith
  · intro h x z lambda hlambda
    have hs := h x z lambda hlambda
    rw [← mul_max_of_nonneg (g x) (g z) hk.le]
    nlinarith

theorem PhiSigned_smul_signedLift_eq_columnPhi
    {I : Type u} [Fintype I] [Nonempty I]
    (tau : ProbabilityMeasure Param) (t : ℝ) (x : ConeVec I) :
    PhiSigned (t • signedLift tau.toFiniteMeasure) x = columnPhi t tau x := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [PhiSigned_of_ne _ x hx, columnPhi_of_ne t tau x hx,
      integratedEntropySigned_smul, integratedEntropySigned_signedLift]
    rfl

theorem GSigned_neg_smul_signedLift_eq_mul_gTrop
    {I : Type u} [Fintype I] [Nonempty I]
    (tau : ProbabilityMeasure Param) (k : ℝ) (z : PosConeVec I) :
    GSigned ((-k) • signedLift tau.toFiniteMeasure) z = k * gTrop tau z := by
  unfold GSigned
  rw [integratedEntropySigned_smul, integratedEntropySigned_signedLift]
  change (-k) * integratedEntropyPos (probMeasure tau) (normalize z) = _
  simp only [gTrop, aTrop]
  ring

/-- Literal bridge between signed scalar witnesses and candidate columns. -/
theorem signedScalarColumnBridge
    {I : Type u} [Fintype I] [Nonempty I]
    (tau : ProbabilityMeasure Param) :
    (∀ (t : ℝ) (x : ConeVec I),
      PhiSigned (t • signedLift tau.toFiniteMeasure) x = columnPhi t tau x) ∧
      (∀ (k : ℝ), 0 < k → ∀ z : PosConeVec I,
        GSigned ((-k) • signedLift tau.toFiniteMeasure) z = k * gTrop tau z) ∧
      (∀ (k : ℝ), 0 < k →
        (QCvx (gTrop tau : PosConeVec I → ℝ) ↔
          QCvx (fun z : PosConeVec I =>
            GSigned ((-k) • signedLift tau.toFiniteMeasure) z))) := by
  refine ⟨fun t x => PhiSigned_smul_signedLift_eq_columnPhi tau t x,
    fun k _hk z => GSigned_neg_smul_signedLift_eq_mul_gTrop tau k z, ?_⟩
  intro k hk
  have hfun : (fun z : PosConeVec I =>
      GSigned ((-k) • signedLift tau.toFiniteMeasure) z) =
      fun z => k * gTrop tau z := by
    funext z
    exact GSigned_neg_smul_signedLift_eq_mul_gTrop tau k z
  rw [hfun]
  exact (qcvx_pos_mul_iff (gTrop tau : PosConeVec I → ℝ) hk).symm

end ConditionalEntropy
