import ConditionalEntropy.Discretization
import ConditionalEntropy.EndpointParameterContinuity

/-!
# Canonical facades for Appendix A.3 and A.6

This module isolates exact manuscript-level statements for endpoint-aware
Rényi continuity and common finite-range discretization. The final
shape-preservation sentence of A.6 is the separate canonical theorem A.7.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

private theorem continuous_renyi_of_pos
    {I : Type u} [Fintype I] [Nonempty I]
    (p : ProbVec I) (hp : ∀ i, 0 < p.1 i) :
    Continuous (fun a : Param => renyi a p) := by
  classical
  let L : PositiveLineData I :=
    { x := p.1
      u := fun _ => 0
      x_pos := hp }
  obtain ⟨istar, histar⟩ := finMax_mem p.1
  have hpos : ∀ lambda ∈ Icc (-1 : ℝ) 1, LinePositive L lambda := by
    intro lambda _hlambda i
    simpa [L, lineRaw] using hp i
  have hfixed : FixedMaxCoordinate L (Icc (-1 : ℝ) 1) istar := by
    intro lambda hlambda
    refine ⟨hpos lambda hlambda, ?_, ?_⟩
    · intro i
      simpa [L, lineRaw, histar] using le_finMax p i
    · intro i _hi
      simp [L, effectiveVelocity]
  have hjoint :=
    (continuousOn_entropyLine_full_bundle L (by norm_num) hpos hfixed).1
  have hslice : Continuous (fun a : Param => entropyLine L a 0) := by
    have hpair : Continuous (fun a : Param => (a, (0 : ℝ))) :=
      continuous_id.prodMk continuous_const
    have hcomp : ContinuousOn
        ((fun p : Param × ℝ => entropyLine L p.1 p.2) ∘
          fun a : Param => (a, (0 : ℝ))) Set.univ :=
      hjoint.comp (s := Set.univ) hpair.continuousOn (by
      intro a _ha
      exact ⟨mem_univ a, by norm_num⟩)
    change Continuous
      ((fun p : Param × ℝ => entropyLine L p.1 p.2) ∘
        fun a : Param => (a, (0 : ℝ)))
    exact continuousOn_univ.mp hcomp
  have hline : ∀ a : Param, entropyLine L a 0 = renyi a p := by
    intro a
    unfold entropyLine
    congr 1
    rw [lineProb_of_positive L 0 (linePositiveZero L)]
    apply Subtype.ext
    funext i
    rw [normalize_apply]
    simp only [linePosCone, lineCone]
    have hraw : lineRaw L 0 = p.1 := by
      funext j
      simp [L, lineRaw]
    rw [hraw]
    change p.1 i / l1Mass p.1 = p.1 i
    rw [p.2.2, div_one]
  exact hslice.congr hline

/-- Appendix A.3: endpoint-aware Rényi entropy is continuous on the whole
compactified parameter interval and has the sharp support-cardinality bound. -/
theorem fullDetailsAppendixA_3
    {I : Type u} [Fintype I] [Nonempty I] (p : ProbVec I) :
    Continuous (fun a : Param => renyi a p) ∧
      (∀ a : Param,
        0 ≤ renyi a p ∧
          renyi a p ≤ Real.log ((supportFinset p.1).card : ℝ)) ∧
      Real.log ((supportFinset p.1).card : ℝ) ≤
        Real.log (Fintype.card I : ℝ) := by
  classical
  let S := {i : I // i ∈ supportFinset p.1}
  letI : Fintype S := by
    dsimp [S]
    exact (supportFinset p.1).fintypeCoeSort
  letI : Nonempty S := by
    obtain ⟨i, hi⟩ := supportFinset_nonempty p
    exact ⟨⟨i, hi⟩⟩
  let ps : ProbVec S :=
    ⟨fun i => p.1 i.1, ⟨fun i => p.2.1 i.1, by
      change (∑ i : S, p.1 i.1) = 1
      have hs : ∑ i : S, p.1 i.1 = ∑ i ∈ supportFinset p.1, p.1 i := by
        exact (Finset.sum_subtype (supportFinset p.1) (fun _ => Iff.rfl) p.1).symm
      rw [hs]
      have hfull : ∑ i ∈ supportFinset p.1, p.1 i = ∑ i, p.1 i := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        simpa only [supportFinset, Finset.mem_filter, Finset.mem_univ,
          true_and, not_ne_iff] using hi
      rw [hfull]
      simpa only [l1Mass] using p.2.2⟩⟩
  let e : S ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  have hpspos : ∀ i : S, 0 < ps.1 i := by
    intro i
    have hne : p.1 i.1 ≠ 0 := by
      simpa only [supportFinset, Finset.mem_filter, Finset.mem_univ,
        true_and] using i.2
    exact lt_of_le_of_ne (p.2.1 i.1) (Ne.symm hne)
  have he : zeroExtendProb e ps = p := by
    apply Subtype.ext
    funext i
    change zeroExtendRaw e ps.1 i = p.1 i
    by_cases hi : i ∈ supportFinset p.1
    · let j : S := ⟨i, hi⟩
      simpa [e, ps, j] using zeroExtendRaw_apply e ps.1 j
    · have hrange : i ∉ Set.range e := by
        rintro ⟨j, hj⟩
        exact hi (hj ▸ j.2)
      have hpzero : p.1 i = 0 := by
        simpa only [supportFinset, Finset.mem_filter, Finset.mem_univ,
          true_and, not_ne_iff] using hi
      simp [zeroExtendRaw, hrange, hpzero]
  have hrenyi : (fun a : Param => renyi a p) =
      fun a => renyi a ps := by
    funext a
    rw [← he, renyi_zeroExtend]
  refine ⟨?_, ?_, ?_⟩
  · rw [hrenyi]
    exact continuous_renyi_of_pos ps hpspos
  · intro a
    exact ⟨renyi_nonneg a p, renyi_le_log_support a p⟩
  · have hspos : 0 < ((supportFinset p.1).card : ℝ) := by
      exact_mod_cast supportFinset_card_pos p
    have hdpos : 0 < (Fintype.card I : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have hcard : ((supportFinset p.1).card : ℝ) ≤
        (Fintype.card I : ℝ) := by
      exact_mod_cast Finset.card_le_univ (s := supportFinset p.1)
    exact Real.strictMonoOn_log.monotoneOn hspos hdpos hcard

/-- Appendix A.6: a common sequence of finite-range measurable parameter
maps gives push-forward integral convergence for every finite probability
vector. The same sequence is therefore available simultaneously at every
point of a finite shape inequality. -/
theorem fullDetailsAppendixA_6
    {I : Type u} [Fintype I] [Nonempty I]
    (p : ProbVec I) (tau : Measure Param) [IsFiniteMeasure tau]
    (T : ℕ → Param → Param)
    (hT : ∀ n, Measurable (T n))
    (_hfinite : ∀ n, Set.Finite (Set.range (T n)))
    (hlim : ∀ᵐ a ∂tau, Tendsto (fun n => T n a) atTop (nhds a)) :
    ((∀ n, ∫ b, renyi b p ∂(Measure.map (T n) tau) =
          ∫ a, renyi (T n a) p ∂tau) ∧
        Tendsto (fun n => ∫ b, renyi b p ∂(Measure.map (T n) tau))
          atTop (nhds (∫ a, renyi a p ∂tau))) ∧
      (∀ (q r : ProbVec I) (lambda : ℝ)
          (hlambda : lambda ∈ Icc (0 : ℝ) 1),
        Tendsto
          (fun n =>
            ((∫ b, renyi b (mixProbVec lambda hlambda q r)
                ∂(Measure.map (T n) tau)),
              ((∫ b, renyi b q ∂(Measure.map (T n) tau)),
                (∫ b, renyi b r ∂(Measure.map (T n) tau)))))
          atTop
          (nhds
            ((∫ a, renyi a (mixProbVec lambda hlambda q r) ∂tau),
              ((∫ a, renyi a q ∂tau), (∫ a, renyi a r ∂tau))))) := by
  have hsingle : ∀ q : ProbVec I,
      ((∀ n, ∫ b, renyi b q ∂(Measure.map (T n) tau) =
            ∫ a, renyi (T n a) q ∂tau) ∧
        Tendsto (fun n => ∫ b, renyi b q ∂(Measure.map (T n) tau))
          atTop (nhds (∫ a, renyi a q ∂tau))) := by
    intro q
    have hcont : Continuous (fun a : Param => renyi a q) :=
      (fullDetailsAppendixA_3 q).1
    have hpoint : ∀ᵐ a ∂tau,
        Tendsto (fun n => renyi (T n a) q) atTop (nhds (renyi a q)) := by
      filter_upwards [hlim] with a ha
      exact (hcont.tendsto a).comp ha
    have hmeas : ∀ n,
        AEStronglyMeasurable (fun a => renyi (T n a) q) tau := by
      intro n
      exact ((measurable_renyi q).comp (hT n)).aestronglyMeasurable
    let C : ℝ := Real.log (Fintype.card I : ℝ)
    have hbound : ∀ n, ∀ᵐ a ∂tau, ‖renyi (T n a) q‖ ≤ C := by
      intro n
      exact Filter.Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (renyi_nonneg (T n a) q)]
        exact renyi_le_log_card (T n a) q
    have hdct : Tendsto (fun n => ∫ a, renyi (T n a) q ∂tau) atTop
        (nhds (∫ a, renyi a q ∂tau)) :=
      tendsto_integral_of_dominated_convergence
        (fun _ : Param => C) hmeas (integrable_const C) hbound hpoint
    constructor
    · intro n
      exact integral_map (hT n).aemeasurable
        (measurable_renyi q).aestronglyMeasurable
    · refine hdct.congr' (Filter.Eventually.of_forall fun n => ?_)
      exact (integral_map (hT n).aemeasurable
        (measurable_renyi q).aestronglyMeasurable).symm
  refine ⟨hsingle p, ?_⟩
  intro q r lambda hlambda
  simpa only [nhds_prod_eq] using
    (hsingle (mixProbVec lambda hlambda q r)).2.prodMk
      ((hsingle q).2.prodMk (hsingle r).2)

end ConditionalEntropy
