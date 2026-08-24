import ConditionalEntropy.BlockLocalizationInterfaces
import ConditionalEntropy.CurvatureObstructions
import ConditionalEntropy.NecessityMeasureAlgebra
import ConditionalEntropy.NullThresholds
import ConditionalEntropy.ShapeReduction
import ConditionalEntropy.ShannonWitnessBridge
import ConditionalEntropy.ULiftInvariance

/-!
# Independent positive-temperate necessity lemmas

This file contains the two-block and scaling parts of positive-temperate
necessity.  The Shannon-atom clause is kept separate until the Shannon
localization theorem is available.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

private theorem positiveBlockCurvatureContradiction
    {J : ℕ} (B : BlockData J) (nu : FiniteMeasure Param)
    (hconc : PosPhiConcave.{u} nu) (v : Fin (J + 1) → ℝ)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop)
    (a b : ℝ)
    (hfirst : Tendsto
      (fun n ↦ blockLogKernel (positiveSigned nu) B n v 1)
      atTop (𝓝 a))
    (hsecond : Tendsto
      (fun n ↦ blockLogKernel (positiveSigned nu) B n v 2)
      atTop (𝓝 b))
    (hcurv : 0 < b + a ^ 2) : False := by
  let phi : ℕ → ℝ → ℝ := fun n lambda ↦
    blockPhiCurve (positiveSigned nu) B n v lambda
  have hsmooth : ∀ n, ∃ epsilon : ℝ, 0 < epsilon ∧ 0 < phi n 0 ∧
      ContDiffOn ℝ 2 (phi n) (Ioo (-epsilon) epsilon) := by
    intro n
    obtain ⟨epsilon, hepsilon, _hpos, hphi0, hdiff, _hGdiff,
      _hlog, _hG⟩ :=
      blockCurveKernelBridge B (positiveSigned nu) n v jTop hTop
    exact ⟨epsilon, hepsilon, hphi0, by simpa only [phi] using hdiff⟩
  have hfirstEq : ∀ n,
      deriv (fun lambda ↦ Real.log (phi n lambda)) 0 =
        blockLogKernel (positiveSigned nu) B n v 1 := by
    intro n
    obtain ⟨_epsilon, _hepsilon, _hpos, _hphi0, _hdiff, _hGdiff,
      hlog, _hG⟩ :=
      blockCurveKernelBridge B (positiveSigned nu) n v jTop hTop
    have h := hlog 1 (by norm_num)
    change deriv
      (fun lambda ↦ Real.log
        (blockPhiCurve (positiveSigned nu) B n v lambda)) 0 =
          blockLogKernel (positiveSigned nu) B n v 1 at h
    simpa only [phi] using h
  have hsecondEq : ∀ n,
      secondDeriv (fun lambda ↦ Real.log (phi n lambda)) 0 =
        blockLogKernel (positiveSigned nu) B n v 2 := by
    intro n
    obtain ⟨_epsilon, _hepsilon, _hpos, _hphi0, _hdiff, _hGdiff,
      hlog, _hG⟩ :=
      blockCurveKernelBridge B (positiveSigned nu) n v jTop hTop
    have h := hlog 2 (by norm_num)
    change secondDeriv
      (fun lambda ↦ Real.log
        (blockPhiCurve (positiveSigned nu) B n v lambda)) 0 =
          blockLogKernel (positiveSigned nu) B n v 2 at h
    simpa only [phi] using h
  have hfirst' : Tendsto
      (fun n ↦ deriv (fun lambda ↦ Real.log (phi n lambda)) 0)
      atTop (𝓝 a) :=
    hfirst.congr' (Filter.Eventually.of_forall fun n ↦ (hfirstEq n).symm)
  have hsecond' : Tendsto
      (fun n ↦ secondDeriv (fun lambda ↦ Real.log (phi n lambda)) 0)
      atTop (𝓝 b) :=
    hsecond.congr' (Filter.Eventually.of_forall fun n ↦ (hsecondEq n).symm)
  have hlineConcave : ∀ n, ∃ epsilon : ℝ, 0 < epsilon ∧
      ConcaveOn ℝ (Ioo (-epsilon) epsilon) (phi n) := by
    intro n
    obtain ⟨epsilon, hepsilon, hpos, _hphi0, _hdiff, _hGdiff,
      _hlog, _hG⟩ :=
      blockCurveKernelBridge B (positiveSigned nu) n v jTop hTop
    letI := blockCarrierNonempty B n
    have hconeLift : ConcaveCone
        (PhiSigned (positiveSigned nu) :
          ConeVec (ULift.{u} (BlockCarrier B n)) → ℝ) := hconc
    have hcone : ConcaveCone
        (PhiSigned (positiveSigned nu) :
          ConeVec (BlockCarrier B n) → ℝ) := by
      exact concaveCone_PhiSigned_of_ulift (positiveSigned nu) hconeLift
    have hline :=
      (coneAffineLineBridge (blockLineData B n v)
        (Ioo (-epsilon) epsilon) (convex_Ioo (-epsilon) epsilon) hpos
        (PhiSigned (positiveSigned nu))).1 hcone
    refine ⟨epsilon, hepsilon, ?_⟩
    simpa only [phi, blockPhiCurve] using hline
  exact (typedLogCurvatureContradiction phi a b hsmooth hfirst' hsecond').1
    hcurv hlineConcave

/-- A positive witness cannot have positive mass in a tail beginning at a
null threshold strictly above order one. -/
theorem positiveUpperTailObstruction
    (nu : FiniteMeasure Param) (hconc : PosPhiConcave.{u} nu)
    {r : ℝ} (hr : 1 < r)
    (hnull : finiteMeasure nu ({finiteParam r} : Set Param) = 0)
    (htail : 0 < finiteMeasure nu (Ioi (finiteParam r))) : False := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hr1 : r ≠ 1 := ne_of_gt hr
  let R : ℝ := r + 1
  have hR : r < R := by dsimp only [R]; linarith
  let mu := positiveSigned nu
  let A := upperMoment mu r
  have hA : A < 0 := by
    simpa only [A, mu] using
      upperMoment_positiveSigned_neg_of_tail nu hr htail
  let B := twoBlockData r R hr0 hR
  let v : Fin 2 → ℝ := ![0, 1]
  have hmuNull : signedTV mu ({finiteParam r} : Set Param) = 0 := by
    rw [signedTV_positiveSigned]
    change finiteMeasure nu ({finiteParam r} : Set Param) = 0
    exact hnull
  have hK0 : ({v} : Set (Fin 2 → ℝ)).Nonempty := singleton_nonempty v
  have hK : IsCompact ({v} : Set (Fin 2 → ℝ)) := isCompact_singleton
  have Hloc := twoBlockLocalization mu r R hr0 hr1 hR
    ({v} : Set (Fin 2 → ℝ)) hK0 hK hmuNull
  dsimp only at Hloc
  have Hupper := Hloc.1 hr
  have hfirstRaw := (compactUniformSingleton
    (fun n w ↦ blockLogKernel mu B n w 1)
    (fun w ↦ twoUpperLogFirst mu r w) v).2 Hupper.1
  have hsecondRaw := (compactUniformSingleton
    (fun n w ↦ blockLogKernel mu B n w 2)
    (fun w ↦ twoUpperLogSecond mu r w) v).2 Hupper.2.1
  have hfirst : Tendsto (fun n ↦ blockLogKernel mu B n v 1)
      atTop (𝓝 A) := by
    simpa [twoUpperLogFirst, A, v] using hfirstRaw
  have hsecond : Tendsto (fun n ↦ blockLogKernel mu B n v 2)
      atTop (𝓝 (-A)) := by
    simpa [twoUpperLogSecond, A, v] using hsecondRaw
  apply positiveBlockCurvatureContradiction B nu hconc v 1
    (twoBlockTopUnique r R hr0 hR) A (-A) hfirst hsecond
  nlinarith [sq_nonneg A]

/-- Concavity of every positive signed column excludes all parameter support
strictly above order one. -/
theorem positiveNecessitySupport (nu : FiniteMeasure Param)
    (hconc : PosPhiConcave.{u} nu) :
    suppMeasure (finiteMeasure nu) ⊆ Icc 0 1 := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  intro beta hbeta
  refine ⟨bot_le, ?_⟩
  by_contra hbetaOne
  have hbetaGt : (1 : Param) < beta := lt_of_not_ge hbetaOne
  have htailOne : 0 < finiteMeasure nu (Ioi (1 : Param)) :=
    measure_pos_of_mem_support_open hbeta isOpen_Ioi hbetaGt
  have htailOne' :
      0 < finiteMeasure nu (Ioi (finiteParam (1 : ℝ))) := by
    simpa only [finiteParam_one] using htailOne
  obtain ⟨r, hrRaw, hnull, htail⟩ :=
    exists_null_tail_threshold (finiteMeasure nu) 1 htailOne'
  have hr : 1 < r := by simpa using hrRaw
  exact positiveUpperTailObstruction nu hconc hr hnull htail

/-- Every lower singular integral truncated at a null point below one is
finite. -/
theorem lowerTruncatedLintegral_lt_top (nu : FiniteMeasure Param)
    {r : ℝ} (_hr : 0 < r) (hr1 : r < 1) :
    (∫⁻ a in Iio (finiteParam r), omegaLower a ∂finiteMeasure nu) < ⊤ := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  let C : ℝ := r / (1 - r)
  have hbound : ∀ a ∈ Iio (finiteParam r),
      omegaLower a ≤ ENNReal.ofReal C := by
    intro a ha
    have haTop : a ≠ (⊤ : Param) :=
      ne_top_of_lt (ha.trans_le le_top)
    let x : ℝ := ENNReal.toReal a
    have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
    have hxr : x < r := by
      dsimp only [x]
      exact ENNReal.toReal_lt_of_lt_ofReal ha
    have hx1 : x ≠ 1 := by linarith
    have hback : finiteParam x = a := by
      simpa only [x, paramToReal] using finiteParam_paramToReal a haTop
    have ha1 : a < (1 : Param) := by
      rw [← finiteParam_one]
      exact ha.trans (by
        change ENNReal.ofReal r < ENNReal.ofReal 1
        exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 hr1)
    rw [omegaLower, if_pos ⟨bot_le, ha1⟩, ← hback,
      singularWeight_finite hx0 hx1]
    apply ENNReal.ofReal_le_ofReal
    dsimp only [C]
    exact (div_le_div_iff₀ (by linarith : 0 < 1 - x)
      (by linarith : 0 < 1 - r)).mpr (by nlinarith)
  calc
    (∫⁻ a in Iio (finiteParam r), omegaLower a ∂finiteMeasure nu) ≤
        ∫⁻ _a in Iio (finiteParam r), ENNReal.ofReal C ∂finiteMeasure nu :=
      setLIntegral_mono measurable_const hbound
    _ = ENNReal.ofReal C *
        finiteMeasure nu (Iio (finiteParam r)) :=
      setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (measure_lt_top (finiteMeasure nu) _)

/-- At every null threshold below one, positive-column concavity bounds the
corresponding lower extended singular integral by one. -/
theorem positiveLowerTruncatedLintegral_le_one
    (nu : FiniteMeasure Param) (hconc : PosPhiConcave.{u} nu)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hnull : finiteMeasure nu ({finiteParam r} : Set Param) = 0) :
    (∫⁻ a in Iio (finiteParam r), omegaLower a ∂finiteMeasure nu) ≤
      ENNReal.ofReal 1 := by
  let ell : ENNReal :=
    ∫⁻ a in Iio (finiteParam r), omegaLower a ∂finiteMeasure nu
  have hellTop : ell ≠ ⊤ :=
    (lowerTruncatedLintegral_lt_top nu hr hr1).ne
  let mu := positiveSigned nu
  let A : ℝ := ENNReal.toReal ell
  have hMoment : lowerMoment mu r = A := by
    simpa only [mu, A, ell] using
      (signedWitnessIntegralBridge nu).2.2 r hr hr1
  have hA : A ≤ 1 := by
    by_contra hnot
    have hAgt : 1 < A := lt_of_not_ge hnot
    have hrNe : r ≠ 1 := ne_of_lt hr1
    let R : ℝ := r + 1
    have hR : r < R := by dsimp only [R]; linarith
    let B := twoBlockData r R hr hR
    let v : Fin 2 → ℝ := ![1, 0]
    have hmuNull : signedTV mu ({finiteParam r} : Set Param) = 0 := by
      rw [signedTV_positiveSigned]
      change finiteMeasure nu ({finiteParam r} : Set Param) = 0
      exact hnull
    have hK0 : ({v} : Set (Fin 2 → ℝ)).Nonempty := singleton_nonempty v
    have hK : IsCompact ({v} : Set (Fin 2 → ℝ)) := isCompact_singleton
    have Hloc := twoBlockLocalization mu r R hr hrNe hR
      ({v} : Set (Fin 2 → ℝ)) hK0 hK hmuNull
    dsimp only at Hloc
    have Hlower := Hloc.2 hr1
    have hfirstRaw := (compactUniformSingleton
      (fun n w ↦ blockLogKernel mu B n w 1)
      (fun w ↦ twoLowerLogFirst mu r w) v).2 Hlower.1
    have hsecondRaw := (compactUniformSingleton
      (fun n w ↦ blockLogKernel mu B n w 2)
      (fun w ↦ twoLowerLogSecond mu r w) v).2 Hlower.2.1
    have hfirst : Tendsto (fun n ↦ blockLogKernel mu B n v 1)
        atTop (𝓝 A) := by
      simpa [twoLowerLogFirst, hMoment, A, v] using hfirstRaw
    have hsecond : Tendsto (fun n ↦ blockLogKernel mu B n v 2)
        atTop (𝓝 (-A)) := by
      simpa [twoLowerLogSecond, hMoment, A, v] using hsecondRaw
    apply positiveBlockCurvatureContradiction B nu hconc v 1
      (twoBlockTopUnique r R hr hR) A (-A) hfirst hsecond
    nlinarith [sq_nonneg A]
  change ell ≤ ENNReal.ofReal 1
  rw [← ENNReal.ofReal_toReal hellTop]
  exact ENNReal.ofReal_le_ofReal hA

/-- Monotone convergence along null thresholds upgrades all truncated lower
bounds to the full extended lower-moment bound. -/
theorem positiveNecessityLowerMoment (nu : FiniteMeasure Param)
    (hconc : PosPhiConcave.{u} nu) :
    MLower (finiteMeasure nu) ≤ ENNReal.ofReal 1 := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  obtain ⟨r, hrmono, hr, hrtendsto⟩ :=
    exists_null_seq_below_one (finiteMeasure nu)
  let f : ℕ → Param → ENNReal := fun n a ↦
    (Iio (finiteParam (r n))).indicator omegaLower a
  have hfmeas : ∀ n, Measurable (f n) := by
    intro n
    exact measurable_omegaLower.indicator measurableSet_Iio
  have hfmono : ∀ a, Monotone (fun n ↦ f n a) := by
    intro a m n hmn
    change f m a ≤ f n a
    have hrle : r m ≤ r n := hrmono.monotone hmn
    have hparam : finiteParam (r m) ≤ finiteParam (r n) :=
      ENNReal.ofReal_le_ofReal hrle
    by_cases ham : a ∈ Iio (finiteParam (r m))
    · have han : a ∈ Iio (finiteParam (r n)) := lt_of_lt_of_le ham hparam
      simp only [f, Set.indicator_of_mem ham, Set.indicator_of_mem han]
      exact le_rfl
    · rw [show f m a = 0 by simp [f, ham]]
      exact bot_le
  have hftendsto : ∀ a,
      Tendsto (fun n ↦ f n a) atTop (𝓝 (omegaLower a)) := by
    intro a
    by_cases haIco : a ∈ Ico (0 : Param) 1
    · have haTop : a ≠ (⊤ : Param) := ne_top_of_lt haIco.2
      let x : ℝ := ENNReal.toReal a
      have hx1 : x < 1 := by
        dsimp only [x]
        exact (ENNReal.toReal_lt_toReal haTop ENNReal.one_ne_top).2 haIco.2
      have hback : finiteParam x = a := by
        simpa only [x, paramToReal] using finiteParam_paramToReal a haTop
      have hevent : ∀ᶠ n in atTop, x < r n :=
        hrtendsto.eventually (Ioi_mem_nhds hx1)
      apply tendsto_const_nhds.congr'
      filter_upwards [hevent] with n hn
      have hmem : a ∈ Iio (finiteParam (r n)) := by
        rw [← hback]
        change ENNReal.ofReal x < ENNReal.ofReal (r n)
        exact (ENNReal.ofReal_lt_ofReal_iff (hr n).1).2 hn
      exact (Set.indicator_of_mem hmem omegaLower).symm
    · have hzero : omegaLower a = 0 := by simp [omegaLower, haIco]
      have hfun : (fun n ↦ f n a) = fun _n : ℕ ↦ (0 : ENNReal) := by
        funext n
        simp [f, hzero]
      rw [hfun, hzero]
      exact tendsto_const_nhds
  have hlim := lintegral_tendsto_of_tendsto_of_monotone
    (μ := finiteMeasure nu)
    (fun n ↦ (hfmeas n).aemeasurable)
    (ae_of_all _ hfmono) (ae_of_all _ hftendsto)
  have hlim' : Tendsto
      (fun n ↦ ∫⁻ a in Iio (finiteParam (r n)), omegaLower a
        ∂finiteMeasure nu)
      atTop (𝓝 (MLower (finiteMeasure nu))) := by
    simpa only [f, lintegral_indicator measurableSet_Iio, MLower] using hlim
  apply le_of_tendsto' hlim'
  intro n
  exact positiveLowerTruncatedLintegral_le_one nu hconc
    (hr n).1 (hr n).2.1 (hr n).2.2

/-- Positive temperate monotonicity transports through the scalar signed
witness to concavity of the scaled positive witness. -/
theorem posPhiConcave_finiteScale_of_CMMonotone
    (tau : ProbabilityMeasure Param) {t : ℝ} (ht : 0 < t)
    (hmono : CMMonotone
      (HTemp t ht.ne' tau : PolyJointFunctional.{u})) :
    PosPhiConcave.{u} (finiteScale t ht.le tau.toFiniteMeasure) := by
  intro I _ _
  have hshape : ConcaveCone (columnPhi t tau : ConeVec I → ℝ) :=
    ((globalTemperateDerivationShapeReduction
      t tau tau.toFiniteMeasure).1 ht).1 hmono
  have hfun :
      (PhiSigned
        (positiveSigned (finiteScale t ht.le tau.toFiniteMeasure)) :
          ConeVec I → ℝ) = columnPhi t tau := by
    funext x
    rw [positiveSigned_finiteScale]
    simpa only [positiveSigned] using
      PhiSigned_smul_signedLift_eq_columnPhi tau t x
  rw [hfun]
  exact hshape

/-- Support, atom, and lower-moment bounds for a positive real scalar
multiple transfer back to the underlying probability measure. -/
theorem positiveFiniteScaleNecessityTransport
    (tau : ProbabilityMeasure Param) {t : ℝ} (ht : 0 < t)
    (hscaled :
      suppMeasure
          (finiteMeasure (finiteScale t ht.le tau.toFiniteMeasure)) ⊆
          Icc 0 1 ∧
        finiteMeasure (finiteScale t ht.le tau.toFiniteMeasure)
            ({1} : Set Param) = 0 ∧
        MLower (finiteMeasure (finiteScale t ht.le tau.toFiniteMeasure)) ≤
          ENNReal.ofReal 1) :
    PosAdm t tau := by
  have hmeasure :
      finiteMeasure (finiteScale t ht.le tau.toFiniteMeasure) =
        ENNReal.ofReal t • probMeasure tau := rfl
  have hscalarPos : 0 < ENNReal.ofReal t := ENNReal.ofReal_pos.mpr ht
  have hsupp :
      suppMeasure
          (finiteMeasure (finiteScale t ht.le tau.toFiniteMeasure)) =
        suppMeasure (probMeasure tau) := by
    rw [hmeasure]
    unfold suppMeasure
    exact support_smul_of_pos _ hscalarPos
  have hatom : probMeasure tau ({1} : Set Param) = 0 := by
    have hprod : ENNReal.ofReal t * probMeasure tau ({1} : Set Param) = 0 := by
      simpa only [hmeasure, Measure.smul_apply, smul_eq_mul] using hscaled.2.1
    exact (mul_eq_zero.mp hprod).resolve_left hscalarPos.ne'
  have hmomentScaled :
      ENNReal.ofReal t * MLower (probMeasure tau) ≤ ENNReal.ofReal 1 := by
    simpa only [hmeasure, MLower_smul] using hscaled.2.2
  have hscalarTop : ENNReal.ofReal t ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmomentDiv :
      MLower (probMeasure tau) ≤
        ENNReal.ofReal 1 / ENNReal.ofReal t := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hscalarPos.ne') (Or.inl hscalarTop)).2
    simpa only [mul_comm] using hmomentScaled
  have hmoment :
      MLower (probMeasure tau) ≤ ENNReal.ofReal (1 / t) := by
    rw [ENNReal.ofReal_div_of_pos ht]
    exact hmomentDiv
  exact ⟨ht, by simpa only [← hsupp] using hscaled.1, hatom, hmoment⟩

end ConditionalEntropy
