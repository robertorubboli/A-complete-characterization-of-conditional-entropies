import ConditionalEntropy.CompactUniformBridge
import ConditionalEntropy.CurvatureObstructions
import ConditionalEntropy.NegativeShannonObstruction
import ConditionalEntropy.ShannonLocalization
import ConditionalEntropy.ShannonKernelRegularityBridge
import ConditionalEntropy.ULiftInvariance

/-!
# Shannon-point obstruction for negative tropical necessity

This module applies corrected finite-index stationarity to the dedicated
Shannon block family.  Its only dependency on the final Shannon localization
proof is isolated in `shannonGCompactUniformPair`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

/-- The finite-index first Shannon `G` kernel, bundled as a continuous linear
functional of the two perturbation coordinates. -/
def shannonGFirstCLM (mu : SignedMeasure Param) (theta : ShannonData)
    (n : ℕ) : (ℝ × ℝ) →L[ℝ] ℝ where
  toFun z := shannonGKernel mu theta n z 1
  map_add' z w := (shannonKernelRegularity mu theta n).1 z w
  map_smul' c z := by
    simpa only [smul_eq_mul, RingHom.id_apply] using
      (shannonKernelRegularity mu theta n).2.1 c z
  cont := (shannonKernelRegularity mu theta n).2.2.1

@[simp] theorem shannonGFirstCLM_apply
    (mu : SignedMeasure Param) (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) :
    shannonGFirstCLM mu theta n z = shannonGKernel mu theta n z 1 := rfl

/-- The limiting first Shannon target, bundled as a continuous linear
functional. -/
def shannonLimitFirstCLM (mu : SignedMeasure Param) (theta : ShannonData) :
    (ℝ × ℝ) →L[ℝ] ℝ where
  toFun z := shannonLimitFirst mu theta z
  map_add' z w := by
    simp only [shannonLimitFirst, Prod.fst_add, Prod.snd_add]
    ring
  map_smul' c z := by
    simp only [shannonLimitFirst, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, RingHom.id_apply]
    ring
  cont := continuous_shannonLimitFirst mu theta

@[simp] theorem shannonLimitFirstCLM_apply
    (mu : SignedMeasure Param) (theta : ShannonData) (z : ℝ × ℝ) :
    shannonLimitFirstCLM mu theta z = shannonLimitFirst mu theta z := rfl

/-- The only direct call site of the final Shannon localization theorem in
this module: its norm-free first and second convergence clauses. -/
private theorem shannonGCompactUniformPair
    (mu : SignedMeasure Param) (theta : ShannonData)
    (K : Set (ℝ × ℝ))
    (hmu : signedTV mu ({finiteParam theta.c} : Set Param) = 0)
    (hK : IsCompact K) (hK0 : K.Nonempty) :
    CompactUniformConverges K
        (fun n z ↦ shannonGKernel mu theta n z 1)
        (shannonLimitFirst mu theta) ∧
      CompactUniformConverges K
        (fun n z ↦ shannonGKernel mu theta n z 2)
        (shannonLimitSecond mu theta) := by
  have Hloc := shannonLocalization mu theta K hmu hK hK0
  exact ⟨Hloc.2.2.1, Hloc.2.2.2⟩

/-- Shannon norm-free localization and kernel regularity assembled into the
stationarity interface used by the corrected quasi-convexity obstruction. -/
theorem shannonGStationarityPackage
    (mu : SignedMeasure Param) (theta : ShannonData)
    (hmu : signedTV mu ({finiteParam theta.c} : Set Param) = 0) :
    StationarityPackage
      (fun n ↦ shannonGFirstCLM mu theta n)
      (shannonLimitFirstCLM mu theta)
      (fun n z ↦ shannonGKernel mu theta n z 2)
      (shannonLimitSecond mu theta) := by
  refine {
    bN_continuous := fun n ↦
      (shannonKernelRegularity mu theta n).2.2.2
    b_continuous := continuous_shannonLimitSecond mu theta
    aN_compactUniform := ?_
    bN_compactUniform := ?_
  }
  · intro K hK hK0
    have H := shannonGCompactUniformPair mu theta K hmu hK hK0
    have ht := compactUniformConverges_tendstoUniformlyOn K hK0 hK
      (fun n z ↦ shannonGKernel mu theta n z 1)
      (shannonLimitFirst mu theta)
      (fun n ↦
        ((shannonKernelRegularity mu theta n).2.2.1).continuousOn)
      (continuous_shannonLimitFirst mu theta).continuousOn H.1
    change TendstoUniformlyOn
      (fun n z ↦ shannonGKernel mu theta n z 1)
      (shannonLimitFirst mu theta) atTop K
    exact ht
  · intro K hK hK0
    have H := shannonGCompactUniformPair mu theta K hmu hK hK0
    exact compactUniformConverges_tendstoUniformlyOn K hK0 hK
      (fun n z ↦ shannonGKernel mu theta n z 2)
      (shannonLimitSecond mu theta)
      (fun n ↦
        ((shannonKernelRegularity mu theta n).2.2.2).continuousOn)
      (continuous_shannonLimitSecond mu theta).continuousOn H.2

/-- Quasi-convexity on the punctured cone restricts to any scalar interval
on which a positive affine line remains positive. -/
private theorem shannonQCvxAffineLine {I : Type*} [Nonempty I]
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
    linePosConeTotal_of_positive L
      (c * x + (1 - c) * y) hmixPos] using hq

/-- Reusable corrected-stationarity contradiction for a dedicated Shannon
`G` curve. -/
theorem shannonGCorrectedObstruction
    (nu : FiniteMeasure Param) (hquasi : NegGQuasiconvex.{u} nu)
    (theta : ShannonData)
    (hnull : finiteMeasure nu
      ({finiteParam theta.c} : Set Param) = 0)
    (v e : ℝ × ℝ)
    (hvFirst : shannonLimitFirst (negativeSigned nu) theta v = 0)
    (hvSecond : shannonLimitSecond (negativeSigned nu) theta v < 0)
    (heFirst : shannonLimitFirst (negativeSigned nu) theta e ≠ 0) :
    False := by
  let mu := negativeSigned nu
  have hmu : signedTV mu
      ({finiteParam theta.c} : Set Param) = 0 := by
    simpa only [mu, signedTV_negativeSigned, finiteMeasure] using hnull
  have hstat := shannonGStationarityPackage mu theta hmu
  have hline : ∀ n z, ∃ eps : ℝ,
      0 < eps ∧
      ContDiffOn ℝ 2 (shannonGCurve mu theta n z)
        (Ioo (-eps) eps) ∧
      ScalarQCvxOn (Ioo (-eps) eps)
        (shannonGCurve mu theta n z) ∧
      deriv (shannonGCurve mu theta n z) 0 =
        shannonGFirstCLM mu theta n z ∧
      secondDeriv (shannonGCurve mu theta n z) 0 =
        shannonGKernel mu theta n z 2 := by
    intro n z
    obtain ⟨eps, heps, hpos, _hphi0, _hPhiSmooth, hGSmooth,
        _hLogKernel, hGKernel⟩ :=
      shannonCurveKernelBridge mu theta n z
    letI := shannonIndexNonempty theta n
    have hqLift : QCvx
        (GSigned mu :
          PosConeVec (ULift.{u} (ShannonIndex theta n)) → ℝ) := hquasi
    have hqCarrier : QCvx
        (GSigned mu : PosConeVec (ShannonIndex theta n) → ℝ) :=
      qCvx_GSigned_of_ulift mu hqLift
    have hscalar : ScalarQCvxOn (Ioo (-eps) eps)
        (shannonGCurve mu theta n z) := by
      change ScalarQCvxOn (Ioo (-eps) eps) (fun lambda ↦
        GSigned mu
          (linePosConeTotal (shannonLineData theta n z) lambda))
      exact shannonQCvxAffineLine (shannonLineData theta n z)
        (Ioo (-eps) eps) hpos (GSigned mu) hqCarrier
    have hfirst := hGKernel 1 (by norm_num)
    change deriv (shannonGCurve mu theta n z) 0 =
      shannonGKernel mu theta n z 1 at hfirst
    have hsecond := hGKernel 2 (by norm_num)
    change secondDeriv (shannonGCurve mu theta n z) 0 =
      shannonGKernel mu theta n z 2 at hsecond
    exact ⟨eps, heps, hGSmooth, hscalar,
      by simpa only [shannonGFirstCLM_apply] using hfirst, hsecond⟩
  apply correctedStationaryLineObstruction
    (fun n z ↦ shannonGCurve mu theta n z)
    (fun n ↦ shannonGFirstCLM mu theta n)
    (shannonLimitFirstCLM mu theta)
    (fun n z ↦ shannonGKernel mu theta n z 2)
    (shannonLimitSecond mu theta) hstat hline v e
  · simpa only [mu, shannonLimitFirstCLM_apply] using hvFirst
  · simpa only [mu] using hvSecond
  · simpa only [mu, shannonLimitFirstCLM_apply] using heFirst

/-- Global negative quasi-convexity forces the Shannon atom to vanish as
soon as the parameter measure has any support strictly above order one. -/
theorem negativeTropicalUpperAtomZero
    (nu : FiniteMeasure Param) (hquasi : NegGQuasiconvex.{u} nu) :
    (suppMeasure (finiteMeasure nu) ∩ Ioi (1 : Param)).Nonempty →
      finiteMeasure nu ({1} : Set Param) = 0 := by
  intro hUpper
  by_contra hatom
  obtain ⟨beta, hbeta, hbetaOne⟩ := hUpper
  obtain ⟨c, hc, hnull, hA⟩ :=
    existsNegativeShannonTailData nu (beta := beta) hbeta hbetaOne
  let mu := negativeSigned nu
  let theta := negativeShannonData c hc
  let v := negativeShannonDirection nu c
  let e : ℝ × ℝ := (0, 1)
  have hm : signedAtom (negativeSigned nu) 1 ≠ 0 :=
    (negativeSignedAtom_one_neg nu hatom).ne
  have htargets := negativeShannonTargets nu hm theta (by
    dsimp only [theta, negativeShannonData])
  have hvFirst : shannonLimitFirst mu theta v = 0 := by
    simpa only [mu, v] using htargets.1
  have hvSecondEq : shannonLimitSecond mu theta v =
      -upperMoment (negativeSigned nu) c := by
    simpa only [mu, v] using htargets.2
  have hvSecond : shannonLimitSecond mu theta v < 0 := by
    rw [hvSecondEq]
    exact neg_neg_of_pos hA
  have heFirstEq : shannonLimitFirst mu theta e =
      upperMoment (negativeSigned nu) c := by
    simp [shannonLimitFirst, shannonTailMoment, mu, theta,
      negativeShannonData, e]
  have heFirst : shannonLimitFirst mu theta e ≠ 0 := by
    rw [heFirstEq]
    exact hA.ne'
  have hnullTheta : finiteMeasure nu
      ({finiteParam theta.c} : Set Param) = 0 := by
    simpa only [theta, negativeShannonData] using hnull
  exact shannonGCorrectedObstruction nu hquasi theta hnullTheta v e
    (by simpa only [mu] using hvFirst)
    (by simpa only [mu] using hvSecond)
    (by simpa only [mu] using heFirst)

end ConditionalEntropy
