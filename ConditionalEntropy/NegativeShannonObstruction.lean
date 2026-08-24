import ConditionalEntropy.NegativeMomentPositivity
import ConditionalEntropy.NullThresholds
import ConditionalEntropy.ShannonCurvatureNecessity

/-!
# Negative Shannon-atom obstruction setup

This file isolates the algebraic and curvature part of the Shannon-point
argument for a negative signed witness.  The final localization theorem only
has to supply the two singleton logarithmic-kernel limits recorded below.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

/-- Deterministic Shannon data attached to a null upper-tail threshold. -/
def negativeShannonData (c : ℝ) (hc : 1 < c) : ShannonData where
  c := c
  R := c + 2
  p := 1 / 2
  c_gt_one := hc
  R_gt := by linarith
  p_pos := by norm_num
  p_lt_one := by norm_num

/-- An upper support point supplies a null Shannon cutoff whose remaining
tail has strictly positive negative-witness moment. -/
theorem existsNegativeShannonTailData (nu : FiniteMeasure Param)
    {beta : Param} (hbeta : beta ∈ suppMeasure (finiteMeasure nu))
    (hbetaOne : (1 : Param) < beta) :
    ∃ c : ℝ, 1 < c ∧
      finiteMeasure nu ({finiteParam c} : Set Param) = 0 ∧
      0 < upperMoment (negativeSigned nu) c := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  have htailOne : 0 < finiteMeasure nu (Ioi (1 : Param)) :=
    measure_pos_of_mem_support_open hbeta isOpen_Ioi hbetaOne
  have htailOne' :
      0 < finiteMeasure nu (Ioi (finiteParam (1 : ℝ))) := by
    simpa only [finiteParam_one] using htailOne
  obtain ⟨c, hcRaw, hnull, htail⟩ :=
    exists_null_tail_threshold (finiteMeasure nu) 1 htailOne'
  have hc : 1 < c := by simpa using hcRaw
  exact ⟨c, hc, hnull,
    upperMoment_negativeSigned_pos_of_tail nu hc htail⟩

/-- A nonzero atom at order one becomes a strictly negative atom of the
canonical negative signed witness. -/
theorem negativeSignedAtom_one_neg (nu : FiniteMeasure Param)
    (hatom : finiteMeasure nu ({1} : Set Param) ≠ 0) :
    signedAtom (negativeSigned nu) 1 < 0 := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  rw [signedAtom_negativeSigned]
  exact neg_lt_zero.mpr <| ENNReal.toReal_pos hatom
    (measure_ne_top (finiteMeasure nu) ({1} : Set Param))

/-- The stationary direction used at a Shannon atom in the presence of a
positive negative-witness upper-tail moment. -/
def negativeShannonDirection (nu : FiniteMeasure Param) (c : ℝ) : ℝ × ℝ :=
  let m := signedAtom (negativeSigned nu) 1
  let A := upperMoment (negativeSigned nu) c
  (-A / m, 1)

/-- The Shannon target pair at the stationary negative direction is exactly
zero and the negative upper-tail moment. -/
theorem negativeShannonTargets (nu : FiniteMeasure Param)
    {c : ℝ} (hm : signedAtom (negativeSigned nu) 1 ≠ 0)
    (theta : ShannonData) (htheta : theta.c = c) :
    shannonLimitFirst (negativeSigned nu) theta
        (negativeShannonDirection nu c) = 0 ∧
      shannonLimitSecond (negativeSigned nu) theta
        (negativeShannonDirection nu c) =
          -upperMoment (negativeSigned nu) c := by
  let m : ℝ := signedAtom (negativeSigned nu) 1
  let A : ℝ := upperMoment (negativeSigned nu) c
  have hm' : m ≠ 0 := by simpa only [m] using hm
  constructor
  · simp only [shannonLimitFirst, shannonTailMoment,
      negativeShannonDirection, htheta]
    field_simp [hm']; ring
  · simp only [shannonLimitSecond, shannonTailMoment,
      negativeShannonDirection, one_pow, mul_one, htheta]

/-- Once singleton localization supplies its target-valued logarithmic
kernel limits, an atom at one together with positive upper-tail moment
contradicts global convexity of the negative signed column. -/
theorem negativeShannonObstruction_of_kernel_limits
    (nu : FiniteMeasure Param) (hconv : NegPhiConvex.{u} nu)
    (hatom : finiteMeasure nu ({1} : Set Param) ≠ 0)
    {c : ℝ} (hc : 1 < c)
    (hupper : 0 < upperMoment (negativeSigned nu) c)
    (hfirst : Tendsto
      (fun n ↦ shannonLogKernel (negativeSigned nu)
        (negativeShannonData c hc) n (negativeShannonDirection nu c) 1)
      atTop
        (𝓝 (shannonLimitFirst (negativeSigned nu)
          (negativeShannonData c hc) (negativeShannonDirection nu c))))
    (hsecond : Tendsto
      (fun n ↦ shannonLogKernel (negativeSigned nu)
        (negativeShannonData c hc) n (negativeShannonDirection nu c) 2)
      atTop
        (𝓝 (shannonLimitSecond (negativeSigned nu)
          (negativeShannonData c hc) (negativeShannonDirection nu c)))) : False := by
  have hmNeg := negativeSignedAtom_one_neg nu hatom
  have hm : signedAtom (negativeSigned nu) 1 ≠ 0 := hmNeg.ne
  have htargets := negativeShannonTargets nu (c := c) hm
    (negativeShannonData c hc) rfl
  have hfirst' : Tendsto
      (fun n ↦ shannonLogKernel (negativeSigned nu)
        (negativeShannonData c hc) n (negativeShannonDirection nu c) 1)
      atTop (𝓝 0) := by
    rw [htargets.1] at hfirst
    exact hfirst
  have hsecond' : Tendsto
      (fun n ↦ shannonLogKernel (negativeSigned nu)
        (negativeShannonData c hc) n (negativeShannonDirection nu c) 2)
      atTop (𝓝 (-upperMoment (negativeSigned nu) c)) := by
    rw [htargets.2] at hsecond
    exact hsecond
  apply negativeShannonCurvatureContradiction nu hconv
    (negativeShannonData c hc) (negativeShannonDirection nu c)
    0 (-upperMoment (negativeSigned nu) c) hfirst' hsecond'
  simpa [pow_two] using neg_neg_of_pos hupper

end ConditionalEntropy
