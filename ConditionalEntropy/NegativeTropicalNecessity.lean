import ConditionalEntropy.LocalizationStationarity
import ConditionalEntropy.NecessityExceptionalMeasureAlgebra
import ConditionalEntropy.NecessityMomentPassage
import ConditionalEntropy.NegativeMomentPositivity
import ConditionalEntropy.NegativeTropicalShannonNecessity
import ConditionalEntropy.NullThresholds
import ConditionalEntropy.TropicalShapeReduction
import ConditionalEntropy.ULiftInvariance

/-!
# Negative-tropical necessity

The measure-theoretic core combines three-block localization with exact
stationarity correction for the normalized signed entropy.  Its
upper-support uniqueness and exceptional truncated-moment steps are
Shannon-independent; the final wrapper imports the dedicated Shannon
obstruction that eliminates the order-one atom.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

/-- Quasi-convexity on the punctured cone restricts to scalar
quasi-convexity along every positive affine line. -/
theorem qCvxAffineLineBridge {I : Type*} [Nonempty I]
    (L : PositiveLineData I) (U : Set ℝ)
    (hUpos : ∀ lambda ∈ U, LinePositive L lambda)
    (g : PosConeVec I → ℝ) (hqcvx : QCvx g) :
    ScalarQCvxOn U (fun lambda ↦ g (linePosConeTotal L lambda)) := by
  intro x hx y hy c hc0 hc1 hmix
  by_cases hcZero : c = 0
  · subst c
    simp
  by_cases hcOne : c = 1
  · subst c
    simp
  have hcPos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hcZero)
  have hcLt : c < 1 := lt_of_le_of_ne hc1 hcOne
  have hxPos := hUpos x hx
  have hyPos := hUpos y hy
  have hmixPos := hUpos (c * x + (1 - c) * y) hmix
  have hposMix :
      posMix c ⟨hcPos, hcLt⟩ (linePosCone L x hxPos)
          (linePosCone L y hyPos) =
        linePosCone L (c * x + (1 - c) * y) hmixPos := by
    apply Subtype.ext
    exact lineCone_mix L x y c ⟨hc0, hc1⟩ hxPos hyPos hmixPos
  have hq := hqcvx (linePosCone L x hxPos) (linePosCone L y hyPos)
    c ⟨hcPos, hcLt⟩
  rw [hposMix] at hq
  simpa only [linePosConeTotal_of_positive L x hxPos,
    linePosConeTotal_of_positive L y hyPos,
    linePosConeTotal_of_positive L (c * x + (1 - c) * y) hmixPos] using hq

/-- Reusable three-block corrected-stationarity contradiction for the
normalized negative signed entropy. -/
theorem threeBlockGCorrectedObstruction
    (nu : FiniteMeasure Param) (hquasi : NegGQuasiconvex.{u} nu)
    (a b R : ℝ) (ha : 0 < a) (hab : a < b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hR : a + b < R)
    (hnullA : finiteMeasure nu ({finiteParam a} : Set Param) = 0)
    (hnullB : finiteMeasure nu ({finiteParam b} : Set Param) = 0)
    (v e : Fin 3 → ℝ)
    (hvFirst : threeGFirst (negativeSigned nu) a b v = 0)
    (hvSecond : threeGSecond (negativeSigned nu) a b v < 0)
    (heFirst : threeGFirst (negativeSigned nu) a b e ≠ 0) : False := by
  let mu := negativeSigned nu
  let B := threeBlockData a b R ha hab hR
  let hTop := threeBlockTopUnique a b R ha hab hR
  have hmu : signedTV mu ({finiteParam a} : Set Param) = 0 ∧
      signedTV mu ({finiteParam b} : Set Param) = 0 := by
    simpa only [mu, signedTV_negativeSigned, finiteMeasure] using
      ⟨hnullA, hnullB⟩
  have hstat := threeBlockGStationarityPackage
    mu a b R ha hab ha1 hb1 hR hmu
  dsimp only at hstat
  have hline : ∀ n w, ∃ eps : ℝ,
      0 < eps ∧
      ContDiffOn ℝ 2 (blockGCurve mu B n w) (Ioo (-eps) eps) ∧
      ScalarQCvxOn (Ioo (-eps) eps) (blockGCurve mu B n w) ∧
      deriv (blockGCurve mu B n w) 0 = blockGFirstCLM mu B n 2 hTop w ∧
      secondDeriv (blockGCurve mu B n w) 0 =
        blockGKernel mu B n w 2 := by
    intro n w
    obtain ⟨eps, heps, hpos, _hphi0, _hPhiSmooth, hGSmooth,
        _hLogKernel, hGKernel⟩ :=
      blockCurveKernelBridge B mu n w 2 hTop
    letI := blockCarrierNonempty B n
    have hqLift : QCvx
        (GSigned mu :
          PosConeVec (ULift.{u} (BlockCarrier B n)) → ℝ) := hquasi
    have hqCarrier : QCvx
        (GSigned mu : PosConeVec (BlockCarrier B n) → ℝ) :=
      qCvx_GSigned_of_ulift mu hqLift
    have hscalar : ScalarQCvxOn (Ioo (-eps) eps)
        (blockGCurve mu B n w) := by
      change ScalarQCvxOn (Ioo (-eps) eps) (fun lambda ↦
        GSigned mu
          (linePosConeTotal (blockLineData B n w) lambda))
      exact qCvxAffineLineBridge (blockLineData B n w)
        (Ioo (-eps) eps) hpos (GSigned mu) hqCarrier
    have hfirst := hGKernel 1 (by norm_num)
    change deriv (blockGCurve mu B n w) 0 =
      blockGKernel mu B n w 1 at hfirst
    have hsecond := hGKernel 2 (by norm_num)
    change secondDeriv (blockGCurve mu B n w) 0 =
      blockGKernel mu B n w 2 at hsecond
    exact ⟨eps, heps, hGSmooth, hscalar,
      by simpa only [blockGFirstCLM_apply] using hfirst, hsecond⟩
  apply correctedStationaryLineObstruction
    (fun n w ↦ blockGCurve mu B n w)
    (fun n ↦ blockGFirstCLM mu B n 2 hTop)
    (threeGFirstCLM mu a b)
    (fun n w ↦ blockGKernel mu B n w 2)
    (threeGSecond mu a b) hstat hline v e
  · change threeGFirst mu a b v = 0
    simpa only [mu] using hvFirst
  · simpa only [mu] using hvSecond
  · change threeGFirst mu a b e ≠ 0
    simpa only [mu] using heFirst

/-- Two distinct upper support points contradict global quasi-convexity of
the normalized negative signed entropy. -/
theorem twoUpperSupportPointsTropicalObstruction
    (nu : FiniteMeasure Param) (hquasi : NegGQuasiconvex.{u} nu)
    {alpha1 alpha2 : Param}
    (halpha1 : alpha1 ∈ suppMeasure (finiteMeasure nu))
    (halpha2 : alpha2 ∈ suppMeasure (finiteMeasure nu))
    (hone : (1 : Param) < alpha1) (horder : alpha1 < alpha2) : False := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  obtain ⟨a, b, ha, haAlpha, hAlphaB, hBAlpha, hnullA, hnullB⟩ :=
    twoUpperNullThresholds (finiteMeasure nu) hone horder
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hab : a < b := by
    have hparam : finiteParam a < finiteParam b := haAlpha.trans hAlphaB
    change ENNReal.ofReal a < ENNReal.ofReal b at hparam
    exact (ENNReal.ofReal_lt_ofReal_iff').mp hparam |>.1
  have ha1 : a ≠ 1 := ne_of_gt ha
  have hb1 : b ≠ 1 := ne_of_gt (ha.trans hab)
  have hmassMiddle :
      0 < finiteMeasure nu (Ioo (finiteParam a) (finiteParam b)) :=
    measure_pos_of_mem_support_open halpha1 isOpen_Ioo ⟨haAlpha, hAlphaB⟩
  have hmassUpper : 0 < finiteMeasure nu (Ioi (finiteParam b)) :=
    measure_pos_of_mem_support_open halpha2 isOpen_Ioi hBAlpha
  let mu := negativeSigned nu
  let A1 := threeCellMoment mu a b 1
  let A2 := upperMoment mu b
  have hA1 : 0 < A1 := by
    simpa only [A1, mu] using
      middleMoment_negativeSigned_pos_of_mass nu ha hab hmassMiddle
  have hA2 : 0 < A2 := by
    simpa only [A2, mu] using
      upperMoment_negativeSigned_pos_of_tail nu (ha.trans hab) hmassUpper
  let R : ℝ := a + b + 1
  have hR : a + b < R := by dsimp only [R]; linarith
  let v : Fin 3 → ℝ := ![0, 1 / A1, -1 / A2]
  let e : Fin 3 → ℝ := ![0, 1, 0]
  have hcell1 : threeCellMoment mu a b 1 = A1 := rfl
  have hcell2 : threeCellMoment mu a b 2 = A2 := rfl
  have hnorm : threeNormBlock a b = 0 := by simp [threeNormBlock, ha]
  have hvFirst : threeGFirst mu a b v = 0 := by
    simp [threeGFirst, hnorm, v, hcell1, hcell2, Fin.sum_univ_three]
    field_simp [hA1.ne', hA2.ne']
    ring
  have hvSecond : threeGSecond mu a b v = -(1 / A1) - (1 / A2) := by
    simp [threeGSecond, hnorm, v, hcell1, hcell2, Fin.sum_univ_three]
    field_simp [hA1.ne', hA2.ne']
    ring
  have hvSecondNeg : threeGSecond mu a b v < 0 := by
    rw [hvSecond]
    have hA1inv : 0 < 1 / A1 := one_div_pos.mpr hA1
    have hA2inv : 0 < 1 / A2 := one_div_pos.mpr hA2
    linarith [hA1inv, hA2inv]
  have heFirst : threeGFirst mu a b e = A1 := by
    simp [threeGFirst, hnorm, e, hcell1, hcell2, Fin.sum_univ_three]
  exact threeBlockGCorrectedObstruction nu hquasi a b R ha0 hab ha1 hb1 hR
    hnullA hnullB v e (by simpa only [mu] using hvFirst)
    (by simpa only [mu] using hvSecondNeg)
    (by simpa only [mu, heFirst] using hA1.ne')

/-- Global negative quasi-convexity permits at most one support point strictly
above order one. -/
theorem oneUpperPointTropical (nu : FiniteMeasure Param)
    (hquasi : NegGQuasiconvex.{u} nu) :
    (suppMeasure (finiteMeasure nu) ∩ Ioi (1 : Param)).Subsingleton := by
  intro alpha1 h1 alpha2 h2
  rcases lt_trichotomy alpha1 alpha2 with h12 | hEq | h21
  · exact False.elim
      (twoUpperSupportPointsTropicalObstruction
        nu hquasi h1.1 h2.1 h1.2 h12)
  · exact hEq
  · exact False.elim
      (twoUpperSupportPointsTropicalObstruction
        nu hquasi h2.1 h1.1 h2.2 h21)

/-- In the exceptional branch, every pair of atom-free lower and upper
cutoffs satisfies the tropical truncated-moment inequality. -/
theorem tropicalTruncatedMoment_of_exceptional
    (nu : FiniteMeasure Param)
    (_hatom : finiteMeasure nu ({1} : Set Param) = 0)
    (hquasi : NegGQuasiconvex.{u} nu)
    {astar : Param} (hastar : (1 : Param) < astar)
    (hsupp : suppMeasure (finiteMeasure nu) ⊆
      Icc (0 : Param) 1 ∪ {astar})
    (hastarSupp : astar ∈ suppMeasure (finiteMeasure nu))
    {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 1 < b)
    (hbastar : finiteParam b < astar)
    (hnullA : finiteMeasure nu ({finiteParam a} : Set Param) = 0)
    (hnullB : finiteMeasure nu ({finiteParam b} : Set Param) = 0) :
    0 ≤ upperTrunc nu b - lowerTrunc nu a := by
  let mu := negativeSigned nu
  let A := upperTrunc nu b
  let B0 := -lowerTrunc nu a
  have hA : 0 < A := by
    simpa only [A] using upperTrunc_pos_of_exceptional_mem_support
      nu hastar hsupp hastarSupp hb hbastar
  by_contra hbound
  have hfail : A + B0 < 0 := by
    have h := lt_of_not_ge hbound
    simpa only [A, B0, sub_eq_add_neg] using h
  let C := -A - B0
  have hC : 0 < C := by
    dsimp only [C]
    linarith [hfail]
  have hab : a < b := ha1.trans hb
  have haNe : a ≠ 1 := ne_of_lt ha1
  have hbNe : b ≠ 1 := ne_of_gt hb
  let R : ℝ := a + b + 1
  have hR : a + b < R := by dsimp only [R]; linarith
  let v : Fin 3 → ℝ := ![0, 1 / C, -1 / A]
  let e : Fin 3 → ℝ := ![0, 0, 1]
  have hcell0 : threeCellMoment mu a b 0 = B0 := by
    have hbridge := (negativeTruncationBridge nu).1 a ha ha1
    simpa only [mu, B0, lowerMoment, threeCellMoment,
      Matrix.cons_val_zero] using hbridge
  have hcell2 : threeCellMoment mu a b 2 = A := by
    have hbridge := (negativeTruncationBridge nu).2 b hb
    change upperMoment mu b = A
    simpa only [mu, A] using hbridge
  have hnorm : threeNormBlock a b = 1 := by
    simp [threeNormBlock, not_lt.mpr ha1.le, hb]
  have hvFirst : threeGFirst mu a b v = 0 := by
    simp [threeGFirst, hnorm, v, hcell0, hcell2, Fin.sum_univ_three]
    field_simp [hC.ne', hA.ne']
    dsimp only [C]
    ring
  have hvSecond : threeGSecond mu a b v = -(1 / C) - (1 / A) := by
    simp [threeGSecond, hnorm, v, hcell0, hcell2, Fin.sum_univ_three]
    field_simp [hC.ne', hA.ne']
    ring
  have hvSecondNeg : threeGSecond mu a b v < 0 := by
    rw [hvSecond]
    have hCinv : 0 < 1 / C := one_div_pos.mpr hC
    have hAinv : 0 < 1 / A := one_div_pos.mpr hA
    linarith [hCinv, hAinv]
  have heFirst : threeGFirst mu a b e = A := by
    simp [threeGFirst, hnorm, e, hcell0, hcell2, Fin.sum_univ_three]
  exact threeBlockGCorrectedObstruction nu hquasi a b R ha hab haNe hbNe hR
    hnullA hnullB v e (by simpa only [mu] using hvFirst)
    (by simpa only [mu] using hvSecondNeg)
    (by simpa only [mu, heFirst] using hA.ne')

/-- Exact negative-tropical measure conclusion once the Shannon atom has
been shown to vanish.  This is the lower-support-or-exceptional core of the
manuscript necessity theorem, before channel monotonicity is transported to
global quasi-convexity. -/
theorem negativeTropicalNecessity_of_atom_zero
    (nu : FiniteMeasure Param) (hquasi : NegGQuasiconvex.{u} nu)
    (hatom : finiteMeasure nu ({1} : Set Param) = 0) :
    suppMeasure (finiteMeasure nu) ⊆ Icc (0 : Param) 1 ∨
      ∃ astar : Param, (1 : Param) < astar ∧
        suppMeasure (finiteMeasure nu) ⊆
          Icc (0 : Param) 1 ∪ {astar} ∧
        finiteMeasure nu ({1} : Set Param) = 0 ∧
        MLower (finiteMeasure nu) < ⊤ ∧
        MomFin (finiteMeasure nu) ∧
        MReal (finiteMeasure nu) ≤ 0 := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  have hupperSubsingleton :
      (suppMeasure (finiteMeasure nu) ∩ Ioi (1 : Param)).Subsingleton :=
    oneUpperPointTropical nu hquasi
  rcases supportLowerOrUniqueUpperWithMem (finiteMeasure nu)
      hupperSubsingleton with hlower |
      ⟨astar, hastarSupp, hastar, hsupp⟩
  · exact Or.inl hlower
  · right
    obtain ⟨b, hb, hbastar, hnullB⟩ :=
      exists_real_null_between_one_upper (finiteMeasure nu) hastar
    have hupper := exceptionalUpperMeasurePackage
      nu hastar hsupp hb hbastar
    let A : ℝ := upperTrunc nu b
    have hMUpper : MUpper (finiteMeasure nu) < ⊤ := hupper.1
    have hAwhole : A =
        ENNReal.toReal (MUpper (finiteMeasure nu)) := by
      simpa only [A] using hupper.2.1
    have hA : 0 ≤ A := by
      simpa only [A] using upperTrunc_nonneg nu hb
    have htruncated : ∀ a : ℝ, 0 < a → a < 1 →
        finiteMeasure nu ({finiteParam a} : Set Param) = 0 →
        0 ≤ A - lowerTrunc nu a := by
      intro a ha ha1 hnullA
      simpa only [A] using tropicalTruncatedMoment_of_exceptional
        nu hatom hquasi hastar hsupp hastarSupp ha ha1 hb hbastar
          hnullA hnullB
    have hlintegralBound : ∀ a : ℝ, 0 < a → a < 1 →
        finiteMeasure nu ({finiteParam a} : Set Param) = 0 →
        (∫⁻ beta in Iio (finiteParam a), omegaLower beta
          ∂finiteMeasure nu) ≤ ENNReal.ofReal A := by
      intro a ha ha1 hnullA
      apply lowerTruncatedLIntegral_le_of_lowerTrunc_le nu ha ha1 hA
      exact sub_nonneg.mp (htruncated a ha ha1 hnullA)
    have hMLowerBound :
        MLower (finiteMeasure nu) ≤ ENNReal.ofReal A :=
      MLower_le_of_null_truncated_lintegrals nu (ENNReal.ofReal A)
        hlintegralBound
    have hMLower : MLower (finiteMeasure nu) < ⊤ :=
      hMLowerBound.trans_lt ENNReal.ofReal_lt_top
    have hMom : MomFin (finiteMeasure nu) := ⟨hMLower, hMUpper⟩
    have hLowerReal :
        ENNReal.toReal (MLower (finiteMeasure nu)) ≤ A := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hMLowerBound
      simpa only [ENNReal.toReal_ofReal hA] using h
    have hMReal : MReal (finiteMeasure nu) ≤ 0 := by
      unfold MReal
      rw [← hAwhole]
      linarith [hLowerReal]
    exact ⟨astar, hastar, hsupp, hatom, hMLower, hMom, hMReal⟩

/-- Channel monotonicity of the negative tropical candidate gives global
quasi-convexity of its canonical negative signed witness. -/
theorem negGQuasiconvex_toFiniteMeasure_of_CMMonotone
    (tau : ProbabilityMeasure Param)
    (hmono : CMMonotone
      (HMinus tau : PolyJointFunctional.{u})) :
    NegGQuasiconvex.{u} tau.toFiniteMeasure := by
  intro I _ _
  have hg : QCvx (gTrop tau : PosConeVec I → ℝ) :=
    ((globalTropicalShapeReduction tau).1.mp hmono)
  have hscaled : QCvx (fun z : PosConeVec I ↦
      GSigned ((-(1 : ℝ)) • signedLift tau.toFiniteMeasure) z) :=
    ((signedScalarColumnBridge (I := I) tau).2.2 1 zero_lt_one).mp hg
  have hsigned : (-(1 : ℝ)) • signedLift tau.toFiniteMeasure =
      negativeSigned tau.toFiniteMeasure := by
    simpa only [negativeSigned] using
      (neg_one_smul ℝ (signedLift tau.toFiniteMeasure))
  rw [hsigned] at hscaled
  exact hscaled

/-- Assembly of negative-tropical necessity from the sole remaining Shannon
input: whenever upper support is nonempty, the order-one atom vanishes.
The dedicated Shannon localization argument will discharge this premise. -/
theorem negativeTropicalNecessity_of_upper_atom_obstruction
    (tau : ProbabilityMeasure Param)
    (hmono : CMMonotone
      (HMinus tau : PolyJointFunctional.{u}))
    (hatom :
      (suppMeasure (finiteMeasure tau.toFiniteMeasure) ∩
          Ioi (1 : Param)).Nonempty →
        finiteMeasure tau.toFiniteMeasure ({1} : Set Param) = 0) :
    DMinus tau := by
  have hquasi : NegGQuasiconvex.{u} tau.toFiniteMeasure :=
    negGQuasiconvex_toFiniteMeasure_of_CMMonotone tau hmono
  unfold DMinus
  by_cases hlower :
      suppMeasure (probMeasure tau) ⊆ Icc (0 : Param) 1
  · exact Or.inl hlower
  · obtain ⟨alpha, halphaSupp, halphaLower⟩ := Set.not_subset.mp hlower
    have halpha : (1 : Param) < alpha := by
      exact lt_of_not_ge (fun hle ↦ halphaLower ⟨bot_le, hle⟩)
    have hUpper :
        (suppMeasure (probMeasure tau) ∩ Ioi (1 : Param)).Nonempty :=
      ⟨alpha, halphaSupp, halpha⟩
    have hUpperFinite :
        (suppMeasure (finiteMeasure tau.toFiniteMeasure) ∩
          Ioi (1 : Param)).Nonempty := by
      change (suppMeasure (probMeasure tau) ∩
        Ioi (1 : Param)).Nonempty
      exact hUpper
    have hatomFinite :
        finiteMeasure tau.toFiniteMeasure ({1} : Set Param) = 0 := by
      exact hatom hUpperFinite
    have hcore := negativeTropicalNecessity_of_atom_zero
      tau.toFiniteMeasure hquasi hatomFinite
    simpa only [NegTropExcAdm, finiteMeasure, probMeasure,
      ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure] using hcore

/-- Complete negative-tropical necessity for a probability parameter
measure. -/
theorem negativeTropicalNecessity
    (tau : ProbabilityMeasure Param) :
    CMMonotone (HMinus tau : PolyJointFunctional.{u}) → DMinus tau := by
  intro hmono
  apply negativeTropicalNecessity_of_upper_atom_obstruction tau hmono
  exact negativeTropicalUpperAtomZero tau.toFiniteMeasure
    (negGQuasiconvex_toFiniteMeasure_of_CMMonotone tau hmono)

end ConditionalEntropy
