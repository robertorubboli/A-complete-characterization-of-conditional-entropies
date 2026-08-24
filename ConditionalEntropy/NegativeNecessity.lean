import ConditionalEntropy.NegativeShannonObstruction
import ConditionalEntropy.NegativeTemperateNecessity
import ConditionalEntropy.ShannonLocalization

/-!
# Complete negative-temperate necessity

The local two- and three-block arguments live in
`NegativeTemperateNecessity`.  This module adds the Shannon-point case and
then transports the exact finite-measure conclusion back to a probability
parameter at a negative temperature.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

private theorem negativeShannonSingletonLimits
    (nu : FiniteMeasure Param) (c : ℝ) (hc : 1 < c)
    (hnull : finiteMeasure nu ({finiteParam c} : Set Param) = 0) :
    let theta := negativeShannonData c hc
    Tendsto
        (fun n ↦ shannonLogKernel (negativeSigned nu) theta n
          (negativeShannonDirection nu c) 1)
        atTop
          (𝓝 (shannonLimitFirst (negativeSigned nu) theta
            (negativeShannonDirection nu c))) ∧
      Tendsto
        (fun n ↦ shannonLogKernel (negativeSigned nu) theta n
          (negativeShannonDirection nu c) 2)
        atTop
          (𝓝 (shannonLimitSecond (negativeSigned nu) theta
            (negativeShannonDirection nu c))) := by
  dsimp only
  let theta := negativeShannonData c hc
  let z := negativeShannonDirection nu c
  let K : Set (ℝ × ℝ) := {z}
  have hmu_c :
      signedTV (negativeSigned nu)
          ({finiteParam theta.c} : Set Param) = 0 := by
    rw [signedTV_negativeSigned]
    change finiteMeasure nu ({finiteParam c} : Set Param) = 0
    exact hnull
  have Hloc := shannonLocalization (negativeSigned nu) theta K hmu_c
    isCompact_singleton (singleton_nonempty z)
  have hfirst := (compactUniformSingleton
    (fun n w ↦ shannonLogKernel (negativeSigned nu) theta n w 1)
    (fun w ↦ shannonLimitFirst (negativeSigned nu) theta w) z).2 Hloc.1
  have hsecond := (compactUniformSingleton
    (fun n w ↦ shannonLogKernel (negativeSigned nu) theta n w 2)
    (fun w ↦ shannonLimitSecond (negativeSigned nu) theta w) z).2 Hloc.2.1
  simpa only [theta, z] using And.intro hfirst hsecond

/-- A nonzero Shannon atom prevents a globally convex negative witness from
having any support strictly above order one. -/
theorem negativeShannonObstruction (nu : FiniteMeasure Param)
    (hatom : finiteMeasure nu ({1} : Set Param) ≠ 0)
    (hconv : NegPhiConvex.{u} nu) :
    suppMeasure (finiteMeasure nu) ⊆ Icc (0 : Param) 1 := by
  intro beta hbeta
  refine ⟨bot_le, ?_⟩
  by_contra hbetaOne
  have hbetaGt : (1 : Param) < beta := lt_of_not_ge hbetaOne
  obtain ⟨c, hc, hnull, hupper⟩ :=
    existsNegativeShannonTailData nu hbeta hbetaGt
  have Hlim := negativeShannonSingletonLimits nu c hc hnull
  exact False.elim <| negativeShannonObstruction_of_kernel_limits
    nu hconv hatom hc hupper Hlim.1 Hlim.2

/-- Global convexity of the canonical negative witness forces the complete
lower-support-or-single-exceptional measure condition. -/
theorem negativeTemperateNecessity (nu : FiniteMeasure Param)
    (hconv : NegPhiConvex.{u} nu) :
    suppMeasure (finiteMeasure nu) ⊆ Icc (0 : Param) 1 ∨
      ∃ astar : Param, (1 : Param) < astar ∧
        suppMeasure (finiteMeasure nu) ⊆
          Icc (0 : Param) 1 ∪ {astar} ∧
        finiteMeasure nu ({1} : Set Param) = 0 ∧
        MLower (finiteMeasure nu) < ⊤ ∧
        MomFin (finiteMeasure nu) ∧
        MReal (finiteMeasure nu) ≤ -1 := by
  by_cases hatom : finiteMeasure nu ({1} : Set Param) = 0
  · exact negativeTemperateNecessity_of_atom_zero nu hconv hatom
  · exact Or.inl (negativeShannonObstruction nu hatom hconv)

/-- Negative-temperate monotonicity for a probability parameter implies the
exact negative admissibility disjunction. -/
theorem negativeTemperateProbabilityNecessity
    (tau : ProbabilityMeasure Param) (t : ℝ) (ht : t < 0) :
    CMMonotone
        (HTemp t (ne_of_lt ht) tau : PolyJointFunctional.{u}) →
      NegLowerAdm t tau ∨ ∃ astar : Param, NegExcAdm t tau astar := by
  intro hmono
  let nu := finiteScale (-t) (neg_nonneg.mpr ht.le) tau.toFiniteMeasure
  have hconv : NegPhiConvex.{u} nu := by
    dsimp only [nu]
    exact negPhiConvex_finiteScale_of_CMMonotone tau ht hmono
  exact negativeFiniteScaleNecessityTransport tau ht
    (negativeTemperateNecessity nu hconv)

end ConditionalEntropy
