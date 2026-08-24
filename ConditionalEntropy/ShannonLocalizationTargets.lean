import ConditionalEntropy.ShannonAtoms
import ConditionalEntropy.SpecialBlockData

/-!
# Shannon localization target polynomials

These are the exact atom and upper-tail expressions appearing in the first
two derivatives of the localized signed column.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ConditionalEntropy

/-- Signed singular moment strictly above the second Shannon crossing. -/
def shannonTailMoment (mu : SignedMeasure Param) (theta : ShannonData) : ℝ :=
  upperMoment mu theta.c

/-- First-order Shannon localization target. -/
def shannonLimitFirst (mu : SignedMeasure Param) (theta : ShannonData)
    (z : ℝ × ℝ) : ℝ :=
  signedAtom mu 1 * z.1 + shannonTailMoment mu theta * z.2

/-- Second-order Shannon localization target. -/
def shannonLimitSecond (mu : SignedMeasure Param) (theta : ShannonData)
    (z : ℝ × ℝ) : ℝ :=
  -shannonTailMoment mu theta * z.2 ^ 2

theorem continuous_shannonLimitFirst (mu : SignedMeasure Param)
    (theta : ShannonData) :
    Continuous (shannonLimitFirst mu theta) := by
  unfold shannonLimitFirst
  fun_prop

theorem continuous_shannonLimitSecond (mu : SignedMeasure Param)
    (theta : ShannonData) :
    Continuous (shannonLimitSecond mu theta) := by
  unfold shannonLimitSecond
  fun_prop

private theorem signedLift_apply_real (nu : FiniteMeasure Param) (a : Param) :
    signedLift nu ({a} : Set Param) =
      ENNReal.toReal (finiteMeasure nu ({a} : Set Param)) := by
  unfold signedLift finiteMeasure
  rw [Measure.toSignedMeasure_apply_measurable (measurableSet_singleton a)]
  rfl

/-- The signed atom of a positive witness is the real mass of the singleton. -/
theorem signedAtom_positiveSigned (nu : FiniteMeasure Param) (a : Param) :
    signedAtom (positiveSigned nu) a =
      ENNReal.toReal (finiteMeasure nu ({a} : Set Param)) := by
  rw [signedAtom_eq_apply]
  unfold positiveSigned signedLift finiteMeasure
  rw [Measure.toSignedMeasure_apply_measurable (measurableSet_singleton a)]
  rfl

/-- The signed atom of a negative witness is minus the real mass of the
singleton. -/
theorem signedAtom_negativeSigned (nu : FiniteMeasure Param) (a : Param) :
    signedAtom (negativeSigned nu) a =
      -ENNReal.toReal (finiteMeasure nu ({a} : Set Param)) := by
  rw [signedAtom_eq_apply]
  unfold negativeSigned
  rw [_root_.neg_apply, signedLift_apply_real]

/-- Literal atom portion of the witness bridge used in both necessity
branches. -/
theorem signedWitnessAtomBridge (nu : FiniteMeasure Param) :
    (∀ a : Param, signedAtom (positiveSigned nu) a =
      ENNReal.toReal (finiteMeasure nu ({a} : Set Param))) ∧
    (∀ a : Param, signedAtom (negativeSigned nu) a =
      -ENNReal.toReal (finiteMeasure nu ({a} : Set Param))) := by
  exact ⟨signedAtom_positiveSigned nu, signedAtom_negativeSigned nu⟩

end ConditionalEntropy
