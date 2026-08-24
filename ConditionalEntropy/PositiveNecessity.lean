import ConditionalEntropy.PositiveShannonAtomNecessity
import ConditionalEntropy.PositiveTemperateNecessity
import ConditionalEntropy.ShannonLocalization

/-!
# Positive temperate necessity

This file assembles the independently verified support and lower-moment
arguments with the dedicated Shannon localization theorem.  The private
singleton wrapper below is the only call site depending on the final
localization API.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

/- The intended localization API has argument order
`mu, theta, K, hmu_c, hK, hK0` and returns the four explicit
compact-uniform error limits.  Keeping that call here makes any final API
adjustment local to this declaration. -/
private theorem positiveShannonSingletonLimits
    (nu : FiniteMeasure Param) (c : ℝ) (hc : 1 < c)
    (hnull :
      finiteMeasure nu ({finiteParam c} : Set Param) = 0) :
    let theta := positiveShannonData c hc
    Tendsto
        (fun n ↦ shannonLogKernel (positiveSigned nu) theta n
          positiveShannonAtomDirection 1)
        atTop
          (𝓝 (shannonLimitFirst (positiveSigned nu) theta
            positiveShannonAtomDirection)) ∧
      Tendsto
        (fun n ↦ shannonLogKernel (positiveSigned nu) theta n
          positiveShannonAtomDirection 2)
        atTop
          (𝓝 (shannonLimitSecond (positiveSigned nu) theta
            positiveShannonAtomDirection)) := by
  dsimp only
  let theta := positiveShannonData c hc
  let z := positiveShannonAtomDirection
  let K : Set (ℝ × ℝ) := {z}
  have hmu_c :
      signedTV (positiveSigned nu)
          ({finiteParam theta.c} : Set Param) = 0 := by
    rw [signedTV_positiveSigned]
    change finiteMeasure nu ({finiteParam c} : Set Param) = 0
    exact hnull
  have Hloc := shannonLocalization (positiveSigned nu) theta K hmu_c
    isCompact_singleton (singleton_nonempty z)
  have hfirstUniform : CompactUniformConverges K
      (fun n w ↦ shannonLogKernel (positiveSigned nu) theta n w 1)
      (fun w ↦ shannonLimitFirst (positiveSigned nu) theta w) := Hloc.1
  have hsecondUniform : CompactUniformConverges K
      (fun n w ↦ shannonLogKernel (positiveSigned nu) theta n w 2)
      (fun w ↦ shannonLimitSecond (positiveSigned nu) theta w) :=
    Hloc.2.1
  have hfirst := (compactUniformSingleton
    (fun n w ↦ shannonLogKernel (positiveSigned nu) theta n w 1)
    (fun w ↦ shannonLimitFirst (positiveSigned nu) theta w) z).2
      hfirstUniform
  have hsecond := (compactUniformSingleton
    (fun n w ↦ shannonLogKernel (positiveSigned nu) theta n w 2)
    (fun w ↦ shannonLimitSecond (positiveSigned nu) theta w) z).2
      hsecondUniform
  simpa only [theta, z] using And.intro hfirst hsecond

/-- Concavity of all positive signed columns forces the exact support,
Shannon-atom, and lower-moment conditions on the representing measure. -/
theorem positiveNecessity (nu : FiniteMeasure Param)
    (hconc : PosPhiConcave.{u} nu) :
    suppMeasure (finiteMeasure nu) ⊆ Icc 0 1 ∧
      finiteMeasure nu ({1} : Set Param) = 0 ∧
      MLower (finiteMeasure nu) ≤ ENNReal.ofReal 1 := by
  have hsupp := positiveNecessitySupport nu hconc
  have hlower := positiveNecessityLowerMoment nu hconc
  have hatom : finiteMeasure nu ({1} : Set Param) = 0 := by
    by_contra hne
    obtain ⟨c, hc, hnull, hkill⟩ :=
      positiveShannonAtomNecessityPackage nu hconc hne
    have Hlim := positiveShannonSingletonLimits nu c hc hnull
    exact hkill Hlim.1 Hlim.2
  exact ⟨hsupp, hatom, hlower⟩

/-- Positive temperate monotonicity for a probability parameter implies
the exact positive admissibility conditions. -/
theorem positiveTemperateProbabilityNecessity
    (tau : ProbabilityMeasure Param) (t : ℝ) (ht : 0 < t) :
    CMMonotone
        (HTemp t (ne_of_gt ht) tau : PolyJointFunctional.{u}) →
      PosAdm t tau := by
  intro hmono
  have hconc :
      PosPhiConcave.{u}
        (finiteScale t ht.le tau.toFiniteMeasure) :=
    posPhiConcave_finiteScale_of_CMMonotone tau ht hmono
  exact positiveFiniteScaleNecessityTransport tau ht
    (positiveNecessity
      (finiteScale t ht.le tau.toFiniteMeasure) hconc)

end ConditionalEntropy
