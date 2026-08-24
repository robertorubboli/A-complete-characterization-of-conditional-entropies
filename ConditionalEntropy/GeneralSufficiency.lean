import ConditionalEntropy.FiniteSupportSufficiency
import ConditionalEntropy.Discretization
import ConditionalEntropy.CurvatureClosure

/-!
# General temperate sufficiency

The three total discretizations use one common approximating measure for all
cone vectors.  Their support and moment packages feed the exact finite-support
theorem, while their dominated-convergence package supplies the pointwise
column limit needed by curvature closure.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

/-- Convergence of every integrated Renyi value implies pointwise convergence
of the corresponding fixed-temperature column perspectives. -/
theorem tendsto_columnPhi_of_integratedEntropy
    {I : Type u} [Fintype I] [Nonempty I]
    (tauN : ℕ → ProbabilityMeasure Param) (tau : ProbabilityMeasure Param)
    (t : ℝ)
    (hent : ∀ p : ProbVec I,
      Tendsto
        (fun n ↦ integratedEntropyPos (probMeasure (tauN n)) p)
        atTop (𝓝 (integratedEntropyPos (probMeasure tau) p))) :
    ∀ x : ConeVec I,
      Tendsto (fun n ↦ columnPhi t (tauN n) x) atTop
        (𝓝 (columnPhi t tau x)) := by
  intro x
  by_cases hx : x = 0
  · subst x
    simpa only [columnPhi_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  · let p : ProbVec I := normalize (toPosCone x hx)
    simp_rw [columnPhi_of_ne _ _ x hx]
    exact tendsto_const_nhds.mul
      ((Real.continuous_exp.continuousAt).tendsto.comp
        (tendsto_const_nhds.mul (hent p)))

/-- Literal arbitrary-measure sufficiency proposition from the blueprint. -/
theorem generalSufficiency
    (tau : ProbabilityMeasure Param) (t : ℝ) (astar : Param)
    {I : Type u} [Fintype I] [Nonempty I] :
    (PosAdm t tau → ConcaveCone (columnPhi (I := I) t tau)) ∧
    (NegLowerAdm t tau → ConvexCone (columnPhi (I := I) t tau)) ∧
    (NegExcAdm t tau astar → ConvexCone (columnPhi (I := I) t tau)) := by
  let atop : UpperParam := ⟨(⊤ : Param), by simp⟩
  letI : IsFiniteMeasure (probMeasure tau) := by
    unfold probMeasure
    infer_instance
  constructor
  · rintro hAdm
    rcases hAdm with ⟨ht, hsupp, hone, hmoment⟩
    have hcurv : ∀ k,
        ConcaveCone (columnPhi (I := I) t (discPos tau k)) := by
      intro k
      rcases (discretization_package tau atop k).1 ⟨hsupp, hone⟩ with
        ⟨hsuppK, honeK, hLowerK, _hUpperK, _hUpper⟩
      have hAdmK : PosAdm t (discPos tau k) :=
        ⟨ht, hsuppK.trans Set.Ico_subset_Icc_self, honeK,
          hLowerK.trans hmoment⟩
      exact (finiteSufficiency (discPos tau k)
        (finite_support_discPos tau k) t astar).1 hAdmK
    apply (pointwiseCurvatureLimit
      (fun k ↦ columnPhi (I := I) t (discPos tau k))
      (columnPhi (I := I) t tau) ?_).1 hcurv
    apply tendsto_columnPhi_of_integratedEntropy (fun k ↦ discPos tau k) tau t
    intro p
    have h := (discretization_dct_package p (probMeasure tau) atop).1
      ⟨hsupp, hone⟩
    refine h.congr' (Filter.Eventually.of_forall fun _ ↦ rfl)
  · constructor
    · rintro hAdm
      rcases hAdm with ⟨ht, hsupp⟩
      have hcurv : ∀ k,
          ConvexCone (columnPhi (I := I) t (discLow tau k)) := by
        intro k
        have hsuppK := (discretization_package tau atop k).2.1 hsupp
        have hAdmK : NegLowerAdm t (discLow tau k) := ⟨ht, hsuppK⟩
        exact (finiteSufficiency (discLow tau k)
          (finite_support_discLow tau k) t astar).2.1 hAdmK
      apply (pointwiseCurvatureLimit
        (fun k ↦ columnPhi (I := I) t (discLow tau k))
        (columnPhi (I := I) t tau) ?_).2 hcurv
      apply tendsto_columnPhi_of_integratedEntropy (fun k ↦ discLow tau k) tau t
      intro p
      have h := (discretization_dct_package p (probMeasure tau) atop).2.1 hsupp
      refine h.congr' (Filter.Eventually.of_forall fun _ ↦ rfl)
    · rintro hAdm
      rcases hAdm with ⟨ht, hastar, hsupp, hone, hLower,
        hMom, hmoment⟩
      let astar' : UpperParam := ⟨astar, hastar⟩
      have hcurv : ∀ k,
          ConvexCone (columnPhi (I := I) t (discExc tau astar' k)) := by
        intro k
        rcases (discretization_package tau astar' k).2.2 ⟨hsupp, hone⟩ with
          ⟨hsuppK, honeK, hLowerK, _hUpperK, hMomK⟩
        rcases hMomK hMom with ⟨hMomFinK, hRealK⟩
        have hsuppK' : suppMeasure (probMeasure (discExc tau astar' k)) ⊆
            Icc (0 : Param) 1 ∪ {astar} := by
          intro a ha
          rcases hsuppK ha with ha | ha
          · exact Or.inl ⟨ha.1, ha.2.le⟩
          · exact Or.inr ha
        have hAdmK : NegExcAdm t (discExc tau astar' k) astar :=
          ⟨ht, hastar, hsuppK', honeK, hLowerK.trans_lt hLower,
            hMomFinK, hRealK.trans hmoment⟩
        exact (finiteSufficiency (discExc tau astar' k)
          (finite_support_discExc tau astar' k) t astar).2.2 hAdmK
      apply (pointwiseCurvatureLimit
        (fun k ↦ columnPhi (I := I) t (discExc tau astar' k))
        (columnPhi (I := I) t tau) ?_).2 hcurv
      apply tendsto_columnPhi_of_integratedEntropy
        (fun k ↦ discExc tau astar' k) tau t
      intro p
      have h := (discretization_dct_package p (probMeasure tau) astar').2.2
        ⟨hsupp, hone⟩
      refine h.congr' (Filter.Eventually.of_forall fun _ ↦ rfl)

end ConditionalEntropy
