import ConditionalEntropy.BlockLocalizationInterfaces
import ConditionalEntropy.CurvatureObstructions
import ConditionalEntropy.NecessityMeasureAlgebra
import ConditionalEntropy.NullThresholds
import ConditionalEntropy.ShapeReduction
import ConditionalEntropy.SignedWitnesses
import ConditionalEntropy.ULiftInvariance

/-!
# Necessity for the derivation branch

The derivation column is definitionally the linear entropy perspective.  The
support obstruction below is proved from the two-block localization package.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

/-- The manuscript's derivation column is the existing linear column
perspective; this abbreviation deliberately creates no second definition. -/
abbrev derivationColumn {I : Type*} [Fintype I] [Nonempty I]
    (nu : FiniteMeasure Param) : ConeVec I → ℝ :=
  columnDeriv nu

/-- On a positive multiplicative line, the derivation column is the raw
mass times the norm-free signed entropy curve. -/
theorem derivationColumn_line_of_positive
    {I : Type*} [Fintype I] [Nonempty I]
    (nu : FiniteMeasure Param) (L : PositiveLineData I)
    {lambda : ℝ} (h : LinePositive L lambda) :
    derivationColumn nu (lineConeTotal L lambda) =
      lineMass L lambda *
        GSigned (positiveSigned nu) (linePosConeTotal L lambda) := by
  have hne : lineCone L lambda h ≠ 0 := by
    intro hzero
    have hmasszero : l1Mass (lineCone L lambda h).1 = 0 := by
      rw [hzero]
      simp [l1Mass]
    rw [l1Mass_lineCone L h] at hmasszero
    exact (lineMass_pos L h).ne' hmasszero
  rw [lineConeTotal_of_positive L lambda h,
    linePosConeTotal_of_positive L lambda h]
  change columnDeriv nu (lineCone L lambda h) = _
  rw [columnDeriv_of_ne nu (lineCone L lambda h) hne,
    l1Mass_lineCone L h]
  have hto : toPosCone (lineCone L lambda h) hne = linePosCone L lambda h := by
    apply Subtype.ext
    rfl
  rw [hto]
  unfold GSigned positiveSigned
  rw [integratedEntropySigned_signedLift]

/-- Block-specialized form of `derivationColumn_line_of_positive`. -/
theorem derivationBlockCurve_eq_mul {J : ℕ}
    (nu : FiniteMeasure Param) (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) {lambda : ℝ}
    (h : LinePositive (blockLineData B n u) lambda) :
    letI := blockCarrierNonempty B n
    derivationColumn nu
        (lineConeTotal (blockLineData B n u) lambda) =
        blockMass B n u lambda *
        blockGCurve (positiveSigned nu) B n u lambda := by
  letI := blockCarrierNonempty B n
  rw [derivationColumn_line_of_positive nu (blockLineData B n u) h,
    blockMass_eq_lineMass]
  unfold blockGCurve
  rfl

/-- Exact second-order product rule in the total `secondDeriv` notation used
by the manuscript. -/
theorem secondDeriv_mul_of_contDiffAt
    {S K : ℝ → ℝ} {x : ℝ}
    (hS : ContDiffAt ℝ 2 S x) (hK : ContDiffAt ℝ 2 K x) :
    secondDeriv (fun y ↦ S y * K y) x =
      secondDeriv S x * K x + 2 * deriv S x * deriv K x +
        S x * secondDeriv K x := by
  have hSdiff : DifferentiableAt ℝ S x := hS.differentiableAt (by norm_num)
  have hKdiff : DifferentiableAt ℝ K x := hK.differentiableAt (by norm_num)
  have hSderiv : DifferentiableAt ℝ (deriv S) x :=
    (hS.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hKderiv : DifferentiableAt ℝ (deriv K) x :=
    (hK.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfirst : deriv (fun y ↦ S y * K y) =ᶠ[𝓝 x]
      fun y ↦ deriv S y * K y + S y * deriv K y := by
    filter_upwards [hS.eventually (by norm_num), hK.eventually (by norm_num)]
      with y hSy hKy
    exact deriv_fun_mul (hSy.differentiableAt (by norm_num))
      (hKy.differentiableAt (by norm_num))
  unfold secondDeriv
  rw [hfirst.deriv_eq]
  change deriv ((deriv S) * K + S * deriv K) x = _
  rw [deriv_add (hSderiv.mul hKdiff) (hSdiff.mul hKderiv),
    deriv_mul hSderiv hKdiff, deriv_mul hSdiff hKderiv]
  ring

private theorem secondDeriv_eq_of_eqOn_open
    {f g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    {x : ℝ} (hx : x ∈ U) (hfg : Set.EqOn f g U) :
    secondDeriv f x = secondDeriv g x := by
  unfold secondDeriv
  have hderiv : deriv f =ᶠ[𝓝 x] deriv g := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact Filter.EventuallyEq.deriv_eq
      (eventuallyEq_of_mem (hU.mem_nhds hy) hfg)
  exact Filter.EventuallyEq.deriv_eq hderiv

private def derivationBlockCurve {J : ℕ}
    (nu : FiniteMeasure Param) (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) (lambda : ℝ) : ℝ := by
  letI := blockCarrierNonempty B n
  exact derivationColumn nu
    (lineConeTotal (blockLineData B n u) lambda)

private def derivationBlockSecond {J : ℕ}
    (nu : FiniteMeasure Param) (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) : ℝ :=
  secondDeriv (derivationBlockCurve nu B n u) 0

private theorem derivationBlockSecondPackage {J : ℕ}
    (nu : FiniteMeasure Param) (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      (∀ lambda ∈ Ioo (-epsilon) epsilon,
        LinePositive (blockLineData B n u) lambda) ∧
      ContDiffOn ℝ 2 (derivationBlockCurve nu B n u)
        (Ioo (-epsilon) epsilon) ∧
      derivationBlockSecond nu B n u / blockMass B n u 0 =
        2 * blockLogMassKernel B n u 1 *
            blockGKernel (positiveSigned nu) B n u 1 +
          blockGKernel (positiveSigned nu) B n u 2 := by
  letI := blockCarrierNonempty B n
  let L := blockLineData B n u
  let S : ℝ → ℝ := lineMass L
  let G : ℝ → ℝ := blockGCurve (positiveSigned nu) B n u
  obtain ⟨epsilon, hepsilon, hpos, _hphi0, _hPhiSmooth,
      hGSmooth, _hLogKernel, hGKernel⟩ :=
    blockCurveKernelBridge B (positiveSigned nu) n u jTop hTop
  let U : Set ℝ := Ioo (-epsilon) epsilon
  have hzero : (0 : ℝ) ∈ U := by
    dsimp only [U]
    constructor <;> linarith
  have hSSmooth : ContDiffOn ℝ 2 S U := by
    dsimp only [S, L]
    unfold lineMass lineRaw
    fun_prop
  have hcurveEq : Set.EqOn (derivationBlockCurve nu B n u)
      (fun lambda => S lambda * G lambda) U := by
    intro lambda hlambda
    change derivationColumn nu
        (lineConeTotal (blockLineData B n u) lambda) =
      lineMass (blockLineData B n u) lambda *
        blockGCurve (positiveSigned nu) B n u lambda
    simpa only [blockMass_eq_lineMass] using
      derivationBlockCurve_eq_mul nu B n u (hpos lambda hlambda)
  have hcurveSmooth : ContDiffOn ℝ 2
      (derivationBlockCurve nu B n u) U :=
    (hSSmooth.mul hGSmooth).congr fun lambda hlambda => hcurveEq hlambda
  have hFSecond : secondDeriv (derivationBlockCurve nu B n u) 0 =
      secondDeriv (fun lambda => S lambda * G lambda) 0 :=
    secondDeriv_eq_of_eqOn_open isOpen_Ioo hzero hcurveEq
  have hSAt : ContDiffAt ℝ 2 S 0 :=
    hSSmooth.contDiffAt (isOpen_Ioo.mem_nhds hzero)
  have hGAt : ContDiffAt ℝ 2 G 0 :=
    hGSmooth.contDiffAt (isOpen_Ioo.mem_nhds hzero)
  have hProduct := secondDeriv_mul_of_contDiffAt hSAt hGAt
  have hSSecond : secondDeriv S 0 = 0 := by
    have hderiv : deriv S = fun _ => ∑ i, L.x i * L.u i := by
      funext lambda
      exact (hasDerivAt_lineMass L lambda).deriv
    unfold secondDeriv
    rw [hderiv]
    simp
  have hratio : deriv S 0 / S 0 = blockLogMassKernel B n u 1 := by
    unfold blockLogMassKernel
    change deriv S 0 / S 0 =
      deriv (fun lambda => Real.log (S lambda)) 0
    have hline := hasDerivAt_lineMass L 0
    rw [(hline.log (lineMass_pos L (linePositiveZero L)).ne').deriv,
      hline.deriv]
  have hGFirst := hGKernel 1 (by norm_num)
  change deriv G 0 = blockGKernel (positiveSigned nu) B n u 1 at hGFirst
  have hGSecond := hGKernel 2 (by norm_num)
  change secondDeriv G 0 =
    blockGKernel (positiveSigned nu) B n u 2 at hGSecond
  have hSpos : 0 < S 0 := lineMass_pos L (linePositiveZero L)
  refine ⟨epsilon, hepsilon, hpos, hcurveSmooth, ?_⟩
  change secondDeriv (derivationBlockCurve nu B n u) 0 / S 0 = _
  rw [hFSecond, hProduct, hSSecond, hGFirst, hGSecond]
  simp only [zero_mul, zero_add]
  calc
    (2 * deriv S 0 * blockGKernel (positiveSigned nu) B n u 1 +
          S 0 * blockGKernel (positiveSigned nu) B n u 2) / S 0 =
        2 * (deriv S 0 / S 0) *
            blockGKernel (positiveSigned nu) B n u 1 +
          blockGKernel (positiveSigned nu) B n u 2 := by
      field_simp [hSpos.ne']
    _ = 2 * blockLogMassKernel B n u 1 *
            blockGKernel (positiveSigned nu) B n u 1 +
          blockGKernel (positiveSigned nu) B n u 2 := by rw [hratio]

/-- Concavity of every derivation column excludes all parameter support
strictly above order one. -/
theorem derivationNecessity.{u} (nu : FiniteMeasure Param)
    (hconcave : ∀ {I : Type u} [Fintype I] [Nonempty I],
      ConcaveCone (derivationColumn nu : ConeVec I → ℝ)) :
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
  let u : Fin 2 → ℝ := ![0, 1]
  have hmuNull : signedTV mu ({finiteParam r} : Set Param) = 0 := by
    have htv := (signedWitnessBridge nu 1 zero_le_one).2.2.1
    rw [htv]
    exact hnull
  have hK0 : ({u} : Set (Fin 2 → ℝ)).Nonempty := singleton_nonempty u
  have hK : IsCompact ({u} : Set (Fin 2 → ℝ)) := isCompact_singleton
  have Hloc := twoBlockLocalization mu r R hr0 hr1 hR
    ({u} : Set (Fin 2 → ℝ)) hK0 hK hmuNull
  dsimp only at Hloc
  have Hupper := Hloc.1 hr
  have hGFirstRaw := (compactUniformSingleton
    (fun n v => blockGKernel mu B n v 1)
    (fun v => twoUpperGFirst mu r v) u).2 Hupper.2.2.1
  have hGSecondRaw := (compactUniformSingleton
    (fun n v => blockGKernel mu B n v 2)
    (fun v => twoUpperGSecond mu r v) u).2 Hupper.2.2.2
  have hGFirst : Tendsto (fun n => blockGKernel mu B n u 1)
      atTop (𝓝 A) := by
    simpa [twoUpperGFirst, A, u] using hGFirstRaw
  have hGSecond : Tendsto (fun n => blockGKernel mu B n u 2)
      atTop (𝓝 (-A)) := by
    simpa [twoUpperGSecond, A, u] using hGSecondRaw
  have hOrderOne := (twoOrderOneDominancePackage r R hr0 hR).1 hr
  have Hmass := (blockLogMassLimit B mu 0 hOrderOne 1
    (twoBlockTopUnique r R hr0 hR)).2
      ({u} : Set (Fin 2 → ℝ)) hK0 hK
  have hMassRaw := (compactUniformSingleton
    (fun n v => blockLogMassKernel B n v 1) (fun v => v 0) u).2 Hmass.1
  have hMass : Tendsto (fun n => blockLogMassKernel B n u 1)
      atTop (𝓝 0) := by
    simpa [u] using hMassRaw
  have hCross : Tendsto (fun n =>
      2 * blockLogMassKernel B n u 1 * blockGKernel mu B n u 1)
      atTop (𝓝 0) := by
    simpa only [mul_assoc, mul_zero, zero_mul] using
      (tendsto_const_nhds.mul (hMass.mul hGFirst) :
        Tendsto (fun n =>
          (2 : ℝ) * (blockLogMassKernel B n u 1 *
            blockGKernel mu B n u 1)) atTop (𝓝 (2 * (0 * A))))
  have hNormalizedEq : ∀ n,
      derivationBlockSecond nu B n u / blockMass B n u 0 =
        2 * blockLogMassKernel B n u 1 * blockGKernel mu B n u 1 +
          blockGKernel mu B n u 2 := by
    intro n
    obtain ⟨_epsilon, _hepsilon, _hpos, _hsmooth, hsecond⟩ :=
      derivationBlockSecondPackage nu B n u 1
        (twoBlockTopUnique r R hr0 hR)
    exact hsecond
  have hNormalized : Tendsto (fun n =>
      derivationBlockSecond nu B n u / blockMass B n u 0)
      atTop (𝓝 (-A)) := by
    simpa only [hNormalizedEq, zero_add] using hCross.add hGSecond
  have hEventuallyPositive : ∀ᶠ n in atTop,
      0 < derivationBlockSecond nu B n u / blockMass B n u 0 :=
    hNormalized.eventually (Ioi_mem_nhds (neg_pos.mpr hA))
  obtain ⟨n, hn⟩ := hEventuallyPositive.exists
  letI := blockCarrierNonempty B n
  obtain ⟨epsilon, hepsilon, hpos, hcurveSmooth, _hsecond⟩ :=
    derivationBlockSecondPackage nu B n u 1
      (twoBlockTopUnique r R hr0 hR)
  let U : Set ℝ := Ioo (-epsilon) epsilon
  have hzero : (0 : ℝ) ∈ U := by
    dsimp only [U]
    constructor <;> linarith
  have hUconvex : Convex ℝ U := by
    simpa only [U] using (convex_Ioo (-epsilon) epsilon)
  have hconeLift : ConcaveCone
      (derivationColumn nu :
        ConeVec (ULift.{u} (BlockCarrier B n)) → ℝ) := hconcave
  have hcone : ConcaveCone
      (derivationColumn nu : ConeVec (BlockCarrier B n) → ℝ) :=
    concaveCone_derivationColumn_of_ulift nu hconeLift
  have hlineConcave : ConcaveOn ℝ U (derivationBlockCurve nu B n u) := by
    have h := (coneAffineLineBridge (blockLineData B n u) U hUconvex
      hpos (derivationColumn nu)).1 hcone
    change ConcaveOn ℝ U (fun lambda => derivationColumn nu
      (lineConeTotal (blockLineData B n u) lambda))
    exact h
  have hnonpos : secondDeriv (derivationBlockCurve nu B n u) 0 ≤ 0 :=
    (lineCurvatureTests U (derivationBlockCurve nu B n u)
      isOpen_Ioo hUconvex hcurveSmooth).1 hlineConcave 0 hzero
  have hmassPos : 0 < blockMass B n u 0 := blockMass_zero_pos B n u
  have hsecondPos : 0 < derivationBlockSecond nu B n u :=
    (div_pos_iff_of_pos_right hmassPos).mp hn
  exact (not_lt_of_ge hnonpos) hsecondPos

end ConditionalEntropy
