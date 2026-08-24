import ConditionalEntropy.NullThresholds
import ConditionalEntropy.ShannonCurvatureNecessity

/-!
# Positive Shannon-atom necessity setup

This module isolates every part of the positive Shannon-atom obstruction
that is independent of the dedicated Shannon localization theorem.  The
final interface asks only for the two pointwise logarithmic-kernel limits
obtained by evaluating compact-uniform localization on a singleton.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

/-- The deterministic Shannon data used for a null threshold above one. -/
def positiveShannonData (c : ℝ) (hc : 1 < c) : ShannonData where
  c := c
  R := c + 2
  p := 1 / 2
  c_gt_one := hc
  R_gt := by linarith
  p_pos := by norm_num
  p_lt_one := by norm_num

/-- The scalar direction which isolates the positive Shannon atom and kills
the upper-tail term in both target polynomials. -/
def positiveShannonAtomDirection : ℝ × ℝ := (1, 0)

/-- Every finite positive measure has a finite real null threshold strictly
above the Shannon parameter. -/
theorem existsPositiveShannonNullThreshold (nu : FiniteMeasure Param) :
    ∃ c : ℝ, 1 < c ∧
      finiteMeasure nu ({finiteParam c} : Set Param) = 0 := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  obtain ⟨s, _hsmono, hs, _hstendsto⟩ :=
    exists_null_seq_above_one (finiteMeasure nu)
  exact ⟨s 0, (hs 0).1, (hs 0).2⟩

/-- A nonzero atom of a finite positive measure gives a strictly positive
signed atom for its canonical positive witness. -/
theorem positiveSignedAtom_one_pos (nu : FiniteMeasure Param)
    (hatom : finiteMeasure nu ({1} : Set Param) ≠ 0) :
    0 < signedAtom (positiveSigned nu) 1 := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  rw [signedAtom_positiveSigned]
  exact ENNReal.toReal_pos hatom
    (measure_ne_top (finiteMeasure nu) ({1} : Set Param))

/-- At direction `(1,0)`, the Shannon target pair is exactly the signed
atom and zero. -/
theorem positiveShannonAtomTargets (nu : FiniteMeasure Param)
    (theta : ShannonData) :
    shannonLimitFirst (positiveSigned nu) theta
        positiveShannonAtomDirection = signedAtom (positiveSigned nu) 1 ∧
      shannonLimitSecond (positiveSigned nu) theta
        positiveShannonAtomDirection = 0 := by
  simp [shannonLimitFirst, shannonLimitSecond,
    positiveShannonAtomDirection]

/-- Once singleton localization supplies its two target-valued kernel
limits, a nonzero positive Shannon atom contradicts global column
concavity. -/
theorem positiveShannonAtomObstruction_of_kernel_limits
    (nu : FiniteMeasure Param) (hconc : PosPhiConcave.{u} nu)
    (hatom : finiteMeasure nu ({1} : Set Param) ≠ 0)
    (theta : ShannonData)
    (hfirst : Tendsto
      (fun n ↦ shannonLogKernel (positiveSigned nu) theta n
        positiveShannonAtomDirection 1)
      atTop
        (𝓝 (shannonLimitFirst (positiveSigned nu) theta
          positiveShannonAtomDirection)))
    (hsecond : Tendsto
      (fun n ↦ shannonLogKernel (positiveSigned nu) theta n
        positiveShannonAtomDirection 2)
      atTop
        (𝓝 (shannonLimitSecond (positiveSigned nu) theta
          positiveShannonAtomDirection))) : False := by
  have htargets := positiveShannonAtomTargets nu theta
  have hfirst' : Tendsto
      (fun n ↦ shannonLogKernel (positiveSigned nu) theta n
        positiveShannonAtomDirection 1)
      atTop (𝓝 (signedAtom (positiveSigned nu) 1)) := by
    simpa only [htargets.1] using hfirst
  have hsecond' : Tendsto
      (fun n ↦ shannonLogKernel (positiveSigned nu) theta n
        positiveShannonAtomDirection 2)
      atTop (𝓝 0) := by
    simpa only [htargets.2] using hsecond
  apply positiveShannonCurvatureContradiction nu hconc theta
    positiveShannonAtomDirection (signedAtom (positiveSigned nu) 1) 0
    hfirst' hsecond'
  simpa only [zero_add] using
    sq_pos_of_pos (positiveSignedAtom_one_pos nu hatom)

/-- Complete positive Shannon-atom setup.  The chosen threshold is null,
the Shannon data are fixed from it, and the only remaining analytic inputs
are the two singleton kernel limits produced by localization. -/
theorem positiveShannonAtomNecessityPackage
    (nu : FiniteMeasure Param) (hconc : PosPhiConcave.{u} nu)
    (hatom : finiteMeasure nu ({1} : Set Param) ≠ 0) :
    ∃ c : ℝ, ∃ hc : 1 < c,
      finiteMeasure nu ({finiteParam c} : Set Param) = 0 ∧
        (let theta := positiveShannonData c hc
         Tendsto
            (fun n ↦ shannonLogKernel (positiveSigned nu) theta n
              positiveShannonAtomDirection 1)
            atTop
              (𝓝 (shannonLimitFirst (positiveSigned nu) theta
                positiveShannonAtomDirection)) →
          Tendsto
            (fun n ↦ shannonLogKernel (positiveSigned nu) theta n
              positiveShannonAtomDirection 2)
            atTop
              (𝓝 (shannonLimitSecond (positiveSigned nu) theta
                positiveShannonAtomDirection)) →
          False) := by
  obtain ⟨c, hc, hnull⟩ := existsPositiveShannonNullThreshold nu
  refine ⟨c, hc, hnull, ?_⟩
  dsimp only
  exact positiveShannonAtomObstruction_of_kernel_limits nu hconc hatom
    (positiveShannonData c hc)

end ConditionalEntropy
