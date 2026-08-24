import ConditionalEntropy.BlockLocalizationInterfaces
import ConditionalEntropy.CurvatureObstructions
import ConditionalEntropy.NecessityExceptionalMeasureAlgebra
import ConditionalEntropy.NecessityMeasureAlgebra
import ConditionalEntropy.NecessityMomentPassage
import ConditionalEntropy.NecessitySupportAlgebra
import ConditionalEntropy.NegativeMomentPositivity
import ConditionalEntropy.NullThresholds
import ConditionalEntropy.ShapeReduction
import ConditionalEntropy.ShannonWitnessBridge
import ConditionalEntropy.ULiftInvariance

/-!
# Negative-temperate necessity

This file develops the convex three-block obstructions for a negative signed
witness.  The Shannon-atom obstruction and the final moment passage are added
after the exact Shannon localization theorem is available.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

/-- A block logarithmic-kernel limit with strictly negative limiting
normalized curvature contradicts convexity of the negative signed column. -/
private theorem negativeBlockCurvatureContradiction
    {J : ℕ} (B : BlockData J) (nu : FiniteMeasure Param)
    (hconv : NegPhiConvex.{u} nu) (v : Fin (J + 1) → ℝ)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop)
    (a b : ℝ)
    (hfirst : Tendsto
      (fun n ↦ blockLogKernel (negativeSigned nu) B n v 1)
      atTop (𝓝 a))
    (hsecond : Tendsto
      (fun n ↦ blockLogKernel (negativeSigned nu) B n v 2)
      atTop (𝓝 b))
    (hcurv : b + a ^ 2 < 0) : False := by
  let phi : ℕ → ℝ → ℝ := fun n lambda ↦
    blockPhiCurve (negativeSigned nu) B n v lambda
  have hsmooth : ∀ n, ∃ epsilon : ℝ, 0 < epsilon ∧ 0 < phi n 0 ∧
      ContDiffOn ℝ 2 (phi n) (Ioo (-epsilon) epsilon) := by
    intro n
    obtain ⟨epsilon, hepsilon, _hpos, hphi0, hdiff, _hGdiff,
      _hlog, _hG⟩ :=
      blockCurveKernelBridge B (negativeSigned nu) n v jTop hTop
    exact ⟨epsilon, hepsilon, hphi0, by simpa only [phi] using hdiff⟩
  have hfirstEq : ∀ n,
      deriv (fun lambda ↦ Real.log (phi n lambda)) 0 =
        blockLogKernel (negativeSigned nu) B n v 1 := by
    intro n
    obtain ⟨_epsilon, _hepsilon, _hpos, _hphi0, _hdiff, _hGdiff,
      hlog, _hG⟩ :=
      blockCurveKernelBridge B (negativeSigned nu) n v jTop hTop
    have h := hlog 1 (by norm_num)
    change deriv
      (fun lambda ↦ Real.log
        (blockPhiCurve (negativeSigned nu) B n v lambda)) 0 =
          blockLogKernel (negativeSigned nu) B n v 1 at h
    simpa only [phi] using h
  have hsecondEq : ∀ n,
      secondDeriv (fun lambda ↦ Real.log (phi n lambda)) 0 =
        blockLogKernel (negativeSigned nu) B n v 2 := by
    intro n
    obtain ⟨_epsilon, _hepsilon, _hpos, _hphi0, _hdiff, _hGdiff,
      hlog, _hG⟩ :=
      blockCurveKernelBridge B (negativeSigned nu) n v jTop hTop
    have h := hlog 2 (by norm_num)
    change secondDeriv
      (fun lambda ↦ Real.log
        (blockPhiCurve (negativeSigned nu) B n v lambda)) 0 =
          blockLogKernel (negativeSigned nu) B n v 2 at h
    simpa only [phi] using h
  have hfirst' : Tendsto
      (fun n ↦ deriv (fun lambda ↦ Real.log (phi n lambda)) 0)
      atTop (𝓝 a) :=
    hfirst.congr' (Filter.Eventually.of_forall fun n ↦ (hfirstEq n).symm)
  have hsecond' : Tendsto
      (fun n ↦ secondDeriv (fun lambda ↦ Real.log (phi n lambda)) 0)
      atTop (𝓝 b) :=
    hsecond.congr' (Filter.Eventually.of_forall fun n ↦ (hsecondEq n).symm)
  have hlineConvex : ∀ n, ∃ epsilon : ℝ, 0 < epsilon ∧
      ConvexOn ℝ (Ioo (-epsilon) epsilon) (phi n) := by
    intro n
    obtain ⟨epsilon, hepsilon, hpos, _hphi0, _hdiff, _hGdiff,
      _hlog, _hG⟩ :=
      blockCurveKernelBridge B (negativeSigned nu) n v jTop hTop
    letI := blockCarrierNonempty B n
    have hcone : ConvexCone
        (PhiSigned (negativeSigned nu) :
          ConeVec (BlockCarrier B n) → ℝ) := by
      apply convexCone_PhiSigned_of_ulift
      exact (hconv : ConvexCone
        (PhiSigned (negativeSigned nu) :
          ConeVec (ULift.{u} (BlockCarrier B n)) → ℝ))
    have hline :=
      (coneAffineLineBridge (blockLineData B n v)
        (Ioo (-epsilon) epsilon)
        (convex_Ioo (-epsilon) epsilon :
          Convex ℝ (Ioo (-epsilon) epsilon)) hpos
        (PhiSigned (negativeSigned nu))).2 hcone
    refine ⟨epsilon, hepsilon, ?_⟩
    simpa only [phi, blockPhiCurve] using hline
  exact (typedLogCurvatureContradiction phi a b hsmooth hfirst' hsecond').2
    hcurv hlineConvex

/-- Two distinct support points strictly above one contradict convexity of
the negative signed column. -/
theorem twoUpperSupportPointsObstruction
    (nu : FiniteMeasure Param) (hconv : NegPhiConvex.{u} nu)
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
    have : finiteParam a < finiteParam b := haAlpha.trans hAlphaB
    change ENNReal.ofReal a < ENNReal.ofReal b at this
    exact (ENNReal.ofReal_lt_ofReal_iff').mp this |>.1
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
  let B := threeBlockData a b R ha0 hab hR
  let v : Fin 3 → ℝ := ![0, 1 / A1, -1 / A2]
  have hmuNull :
      signedTV mu ({finiteParam a} : Set Param) = 0 ∧
        signedTV mu ({finiteParam b} : Set Param) = 0 := by
    simpa only [mu, signedTV_negativeSigned, finiteMeasure] using
      And.intro hnullA hnullB
  have hK0 : ({v} : Set (Fin 3 → ℝ)).Nonempty := singleton_nonempty v
  have hK : IsCompact ({v} : Set (Fin 3 → ℝ)) := isCompact_singleton
  have Hloc := threeBlockLocalization mu a b R ha0 hab ha1 hb1 hR
    ({v} : Set (Fin 3 → ℝ)) hK0 hK hmuNull
  dsimp only at Hloc
  have hfirstRaw := (compactUniformSingleton
    (fun n w ↦ blockLogKernel mu B n w 1)
    (fun w ↦ threeLogFirst mu a b w) v).2 Hloc.1
  have hsecondRaw := (compactUniformSingleton
    (fun n w ↦ blockLogKernel mu B n w 2)
    (fun w ↦ threeLogSecond mu a b w) v).2 Hloc.2.1
  have hcell1 : threeCellMoment mu a b 1 = A1 := rfl
  have hcell2 : threeCellMoment mu a b 2 = A2 := rfl
  have hnorm : threeNormBlock a b = 0 := by simp [threeNormBlock, ha]
  have hfirstLimit : threeLogFirst mu a b v = 0 := by
    simp [threeLogFirst, hnorm, v, hcell1, hcell2, Fin.sum_univ_three]
    field_simp [hA1.ne', hA2.ne']
    ring
  have hsecondLimit :
      threeLogSecond mu a b v = -(1 / A1) - (1 / A2) := by
    simp [threeLogSecond, hnorm, v, hcell1, hcell2, Fin.sum_univ_three]
    field_simp [hA1.ne', hA2.ne']
    ring
  have hfirst : Tendsto (fun n ↦ blockLogKernel mu B n v 1)
      atTop (𝓝 0) := by simpa only [hfirstLimit] using hfirstRaw
  have hsecond : Tendsto (fun n ↦ blockLogKernel mu B n v 2)
      atTop (𝓝 (-(1 / A1) - (1 / A2))) := by
    simpa only [hsecondLimit] using hsecondRaw
  apply negativeBlockCurvatureContradiction B nu hconv v 2
    (threeBlockTopUnique a b R ha0 hab hR) 0
      (-(1 / A1) - (1 / A2)) hfirst hsecond
  have hA1inv : 0 < 1 / A1 := one_div_pos.mpr hA1
  have hA2inv : 0 < 1 / A2 := one_div_pos.mpr hA2
  have hnegative : -(1 / A1) - (1 / A2) < 0 := by linarith
  simpa using hnegative

/-- Convexity of the negative signed column permits at most one support
point strictly above order one. -/
theorem oneUpperPoint (nu : FiniteMeasure Param)
    (hconv : NegPhiConvex.{u} nu) :
    (suppMeasure (finiteMeasure nu) ∩ Ioi (1 : Param)).Subsingleton := by
  intro alpha1 h1 alpha2 h2
  rcases lt_trichotomy alpha1 alpha2 with h12 | hEq | h21
  · exact False.elim
      (twoUpperSupportPointsObstruction nu hconv h1.1 h2.1 h1.2 h12)
  · exact hEq
  · exact False.elim
      (twoUpperSupportPointsObstruction nu hconv h2.1 h1.1 h2.2 h21)

/-- Failure of the truncated moment bound produces a three-block curve with
negative limiting normalized curvature, contradicting convexity. -/
theorem truncatedMoment (nu : FiniteMeasure Param)
    (_hatom : finiteMeasure nu ({1} : Set Param) = 0)
    (hconv : NegPhiConvex.{u} nu) {a b : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb1 : 1 < b)
    (hnullA : finiteMeasure nu ({finiteParam a} : Set Param) = 0)
    (hnullB : finiteMeasure nu ({finiteParam b} : Set Param) = 0)
    (htail : 0 < finiteMeasure nu (Ioi (finiteParam b))) :
    1 ≤ upperTrunc nu b - lowerTrunc nu a ∧
      IntegrableOn singularWeight (Iio (finiteParam a)) (finiteMeasure nu) ∧
      IntegrableOn (fun beta ↦ -singularWeight beta)
        (Ioi (finiteParam b)) (finiteMeasure nu) := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  have hlowInt :
      IntegrableOn singularWeight (Iio (finiteParam a)) (finiteMeasure nu) :=
    (integrable_indicator_iff measurableSet_Iio).mp
      (integrable_singularWeight_Iio (finiteMeasure nu) ha ha1)
  have huppInt :
      IntegrableOn (fun beta ↦ -singularWeight beta)
        (Ioi (finiteParam b)) (finiteMeasure nu) :=
    (integrable_indicator_iff measurableSet_Ioi).mp (by
      have hneg :=
        (integrable_singularWeight_Ioi (finiteMeasure nu) hb1).neg
      apply hneg.congr
      filter_upwards [] with beta
      by_cases hmem : beta ∈ Ioi (finiteParam b) <;> simp [hmem])
  refine ⟨?_, hlowInt, huppInt⟩
  let mu := negativeSigned nu
  let L := lowerTrunc nu a
  let A := upperTrunc nu b
  let B0 := -L
  have hA : 0 < A := by
    have hmom := upperMoment_negativeSigned_pos_of_tail nu hb1 htail
    simpa only [A, (negativeTruncationBridge nu).2 b hb1] using hmom
  have hB0 : B0 ≤ 0 := by
    dsimp only [B0, L]
    exact neg_nonpos.mpr (lowerTrunc_nonneg nu ha ha1)
  by_contra hbound
  have hfail : A + B0 < 1 := by
    have := lt_of_not_ge hbound
    dsimp only [A, B0, L]
    linarith
  let C := 1 - A - B0
  have hC : 0 < C := by dsimp only [C]; linarith
  have hab : a < b := ha1.trans hb1
  have haNe : a ≠ 1 := ne_of_lt ha1
  have hbNe : b ≠ 1 := ne_of_gt hb1
  let R : ℝ := a + b + 1
  have hR : a + b < R := by dsimp only [R]; linarith
  let B := threeBlockData a b R ha hab hR
  let v : Fin 3 → ℝ := ![0, 1 / C, -1 / A]
  have hmuNull :
      signedTV mu ({finiteParam a} : Set Param) = 0 ∧
        signedTV mu ({finiteParam b} : Set Param) = 0 := by
    simpa only [mu, signedTV_negativeSigned, finiteMeasure] using
      And.intro hnullA hnullB
  have hK0 : ({v} : Set (Fin 3 → ℝ)).Nonempty := singleton_nonempty v
  have hK : IsCompact ({v} : Set (Fin 3 → ℝ)) := isCompact_singleton
  have Hloc := threeBlockLocalization mu a b R ha hab haNe hbNe hR
    ({v} : Set (Fin 3 → ℝ)) hK0 hK hmuNull
  dsimp only at Hloc
  have hfirstRaw := (compactUniformSingleton
    (fun n w ↦ blockLogKernel mu B n w 1)
    (fun w ↦ threeLogFirst mu a b w) v).2 Hloc.1
  have hsecondRaw := (compactUniformSingleton
    (fun n w ↦ blockLogKernel mu B n w 2)
    (fun w ↦ threeLogSecond mu a b w) v).2 Hloc.2.1
  have hcell0 : threeCellMoment mu a b 0 = B0 := by
    have hbridge := (negativeTruncationBridge nu).1 a ha ha1
    change lowerMoment mu a = B0
    simpa only [mu, B0, L] using hbridge
  have hcell2 : threeCellMoment mu a b 2 = A := by
    have hbridge := (negativeTruncationBridge nu).2 b hb1
    change upperMoment mu b = A
    simpa only [mu, A] using hbridge
  have hnorm : threeNormBlock a b = 1 := by
    simp [threeNormBlock, not_lt.mpr ha1.le, hb1]
  have hfirstLimit : threeLogFirst mu a b v = 0 := by
    simp [threeLogFirst, hnorm, v, hcell0, hcell2, Fin.sum_univ_three]
    field_simp [hC.ne', hA.ne']
    dsimp only [C]
    ring
  have hsecondLimit :
      threeLogSecond mu a b v = -(1 / C) - (1 / A) := by
    simp [threeLogSecond, hnorm, v, hcell0, hcell2, Fin.sum_univ_three]
    field_simp [hC.ne', hA.ne']
    ring
  have hfirst : Tendsto (fun n ↦ blockLogKernel mu B n v 1)
      atTop (𝓝 0) := by simpa only [hfirstLimit] using hfirstRaw
  have hsecond : Tendsto (fun n ↦ blockLogKernel mu B n v 2)
      atTop (𝓝 (-(1 / C) - (1 / A))) := by
    simpa only [hsecondLimit] using hsecondRaw
  apply negativeBlockCurvatureContradiction B nu hconv v 2
    (threeBlockTopUnique a b R ha hab hR) 0
      (-(1 / C) - (1 / A)) hfirst hsecond
  have hCinv : 0 < 1 / C := one_div_pos.mpr hC
  have hAinv : 0 < 1 / A := one_div_pos.mpr hA
  have hnegative : -(1 / C) - (1 / A) < 0 := by linarith
  simpa using hnegative

/-- Exact negative-temperate necessity once the Shannon atom has been shown
to vanish.  The conclusion is the manuscript's lower-support-or-exceptional
alternative, including both guarded moment finiteness and the sharp real
moment bound. -/
theorem negativeTemperateNecessity_of_atom_zero
    (nu : FiniteMeasure Param) (hconv : NegPhiConvex.{u} nu)
    (hatom : finiteMeasure nu ({1} : Set Param) = 0) :
    suppMeasure (finiteMeasure nu) ⊆ Icc (0 : Param) 1 ∨
      ∃ astar : Param, (1 : Param) < astar ∧
        suppMeasure (finiteMeasure nu) ⊆
          Icc (0 : Param) 1 ∪ {astar} ∧
        finiteMeasure nu ({1} : Set Param) = 0 ∧
        MLower (finiteMeasure nu) < ⊤ ∧
        MomFin (finiteMeasure nu) ∧
        MReal (finiteMeasure nu) ≤ -1 := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  have hupperSubsingleton :
      (suppMeasure (finiteMeasure nu) ∩ Ioi (1 : Param)).Subsingleton :=
    oneUpperPoint nu hconv
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
    have hatomStar : 0 < finiteMeasure nu ({astar} : Set Param) :=
      hupper.2.2.2 hastarSupp
    have htail : 0 < finiteMeasure nu (Ioi (finiteParam b)) := by
      rw [hupper.2.2.1]
      exact hatomStar
    have htruncated : ∀ a : ℝ, 0 < a → a < 1 →
        finiteMeasure nu ({finiteParam a} : Set Param) = 0 →
        1 ≤ A - lowerTrunc nu a := by
      intro a ha ha1 hnullA
      exact (truncatedMoment nu hatom hconv ha ha1 hb
        hnullA hnullB htail).1
    obtain ⟨r, _hrmono, hr, _hrtendsto⟩ :=
      exists_null_seq_below_one (finiteMeasure nu)
    have hsample := htruncated (r 0) (hr 0).1 (hr 0).2.1 (hr 0).2.2
    have hsampleNonneg : 0 ≤ lowerTrunc nu (r 0) :=
      lowerTrunc_nonneg nu (hr 0).1 (hr 0).2.1
    have hAone : 1 ≤ A := by linarith
    have hAminus : 0 ≤ A - 1 := sub_nonneg.mpr hAone
    have hMLowerBound :
        MLower (finiteMeasure nu) ≤ ENNReal.ofReal (A - 1) :=
      MLower_le_of_truncated_difference nu A hAminus htruncated
    have hMLower : MLower (finiteMeasure nu) < ⊤ :=
      hMLowerBound.trans_lt ENNReal.ofReal_lt_top
    have hMom : MomFin (finiteMeasure nu) := ⟨hMLower, hMUpper⟩
    have hLowerReal :
        ENNReal.toReal (MLower (finiteMeasure nu)) ≤ A - 1 := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hMLowerBound
      simpa only [ENNReal.toReal_ofReal hAminus] using h
    have hMReal : MReal (finiteMeasure nu) ≤ -1 := by
      unfold MReal
      rw [← hAwhole]
      linarith
    exact ⟨astar, hastar, hsupp, hatom, hMLower, hMom, hMReal⟩

/-- Negative finite-temperature monotonicity transports to convexity of the
canonical scaled negative witness. -/
theorem negPhiConvex_finiteScale_of_CMMonotone
    (tau : ProbabilityMeasure Param) {t : ℝ} (ht : t < 0)
    (hmono : CMMonotone
      (HTemp t ht.ne tau : PolyJointFunctional.{u})) :
    NegPhiConvex.{u}
      (finiteScale (-t) (neg_nonneg.mpr ht.le) tau.toFiniteMeasure) := by
  intro I _ _
  have hshape : ConvexCone (columnPhi t tau : ConeVec I → ℝ) :=
    ((globalTemperateDerivationShapeReduction
      t tau tau.toFiniteMeasure).2.1 ht).1 hmono
  have hfun :
      (PhiSigned
        (negativeSigned
          (finiteScale (-t) (neg_nonneg.mpr ht.le) tau.toFiniteMeasure)) :
          ConeVec I → ℝ) = columnPhi t tau := by
    funext x
    rw [negativeSigned_finiteScale]
    simpa only [neg_neg, positiveSigned] using
      PhiSigned_smul_signedLift_eq_columnPhi tau t x
  rw [hfun]
  exact hshape

/-- The complete lower/exceptional conclusion for a positive scalar multiple
reflects to the underlying probability measure with the exact `1 / t`
moment bound. -/
theorem negativeFiniteScaleNecessityTransport
    (tau : ProbabilityMeasure Param) {t : ℝ} (ht : t < 0)
    (hscaled :
      suppMeasure
          (finiteMeasure
            (finiteScale (-t) (neg_nonneg.mpr ht.le) tau.toFiniteMeasure)) ⊆
          Icc 0 1 ∨
        ∃ astar : Param, 1 < astar ∧
          suppMeasure
              (finiteMeasure
                (finiteScale (-t) (neg_nonneg.mpr ht.le)
                  tau.toFiniteMeasure)) ⊆
            Icc 0 1 ∪ {astar} ∧
          finiteMeasure
              (finiteScale (-t) (neg_nonneg.mpr ht.le)
                tau.toFiniteMeasure) ({1} : Set Param) = 0 ∧
          MLower
              (finiteMeasure
                (finiteScale (-t) (neg_nonneg.mpr ht.le)
                  tau.toFiniteMeasure)) < ⊤ ∧
          MomFin
              (finiteMeasure
                (finiteScale (-t) (neg_nonneg.mpr ht.le)
                  tau.toFiniteMeasure)) ∧
          MReal
              (finiteMeasure
                (finiteScale (-t) (neg_nonneg.mpr ht.le)
                  tau.toFiniteMeasure)) ≤ -1) :
    NegLowerAdm t tau ∨ ∃ astar : Param, NegExcAdm t tau astar := by
  let c : ℝ := -t
  have hc : 0 < c := by dsimp only [c]; exact neg_pos.mpr ht
  have hmeasure :
      finiteMeasure
          (finiteScale (-t) (neg_nonneg.mpr ht.le) tau.toFiniteMeasure) =
        ENNReal.ofReal c • probMeasure tau := by
    rfl
  have hscalarPos : 0 < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hc
  have hsuppEq :
      suppMeasure
          (finiteMeasure
            (finiteScale (-t) (neg_nonneg.mpr ht.le) tau.toFiniteMeasure)) =
        suppMeasure (probMeasure tau) := by
    rw [hmeasure]
    unfold suppMeasure
    exact support_smul_of_pos _ hscalarPos
  rcases hscaled with hlower | ⟨astar, hastar, hsupp, hatom,
      hLower, hMom, hM⟩
  · left
    exact ⟨ht, by simpa only [← hsuppEq] using hlower⟩
  · right
    refine ⟨astar, ht, hastar, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [← hsuppEq] using hsupp
    · have hprod : ENNReal.ofReal c *
          probMeasure tau ({1} : Set Param) = 0 := by
        simpa only [hmeasure, Measure.smul_apply, smul_eq_mul] using hatom
      exact (mul_eq_zero.mp hprod).resolve_left hscalarPos.ne'
    · have hMomBase : MomFin (probMeasure tau) := by
        apply (MomFin_smul_iff hc (probMeasure tau)).1
        simpa only [hmeasure] using hMom
      exact hMomBase.1
    · apply (MomFin_smul_iff hc (probMeasure tau)).1
      simpa only [hmeasure] using hMom
    · have hscaledMoment : c * MReal (probMeasure tau) ≤ -1 := by
        have hformula := MReal_smul hc.le (probMeasure tau)
        rw [hmeasure, hformula] at hM
        exact hM
      have hdiv : MReal (probMeasure tau) ≤ (-1 : ℝ) / c := by
        apply (le_div_iff₀ hc).2
        simpa only [mul_comm] using hscaledMoment
      have hid : (-1 : ℝ) / c = 1 / t := by
        dsimp only [c]
        field_simp [ht.ne]
      rw [← hid]
      exact hdiv

end ConditionalEntropy
