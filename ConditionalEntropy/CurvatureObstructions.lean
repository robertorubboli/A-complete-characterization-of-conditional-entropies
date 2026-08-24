import ConditionalEntropy.LineData
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Scalar curvature obstructions

This module isolates the closed calculus facts that turn logarithmic
derivative limits into concavity or convexity obstructions.
-/

noncomputable section

open Filter Set SignType
open scoped Topology

namespace ConditionalEntropy

/-- Second scalar-line curvature normalized by the value at the origin. -/
def normalizedCurvature (phi : ℝ → ℝ) : ℝ :=
  secondDeriv phi 0 / phi 0

/-- The normalized curvature of a positive scalar curve is the second
logarithmic derivative plus the square of the first logarithmic derivative. -/
theorem logCurvatureIdentity (phi : ℝ → ℝ) (hphi0 : 0 < phi 0)
    (hphi : ContDiffAt ℝ 2 phi 0) :
    normalizedCurvature phi =
      secondDeriv (fun lambda => Real.log (phi lambda)) 0 +
        deriv (fun lambda => Real.log (phi lambda)) 0 ^ 2 := by
  have hphiDiff : DifferentiableAt ℝ phi 0 :=
    hphi.differentiableAt (by norm_num)
  have hderivDiff : DifferentiableAt ℝ (deriv phi) 0 :=
    (hphi.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hposEventually : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < phi x :=
    hphi.continuousAt.eventually (Ioi_mem_nhds hphi0)
  have hdiffEventually :
      ∀ᶠ x in 𝓝 (0 : ℝ), DifferentiableAt ℝ phi x := by
    filter_upwards [hphi.eventually (by norm_num)] with x hx
    exact hx.differentiableAt (by norm_num)
  have hlogDerivative :
      (fun x => deriv (fun y => Real.log (phi y)) x) =ᶠ[𝓝 (0 : ℝ)]
        fun x => deriv phi x / phi x := by
    filter_upwards [hdiffEventually, hposEventually] with x hdx hpx
    exact deriv.log hdx hpx.ne'
  have hfirst :
      deriv (fun lambda => Real.log (phi lambda)) 0 = deriv phi 0 / phi 0 :=
    (hphiDiff.hasDerivAt.log hphi0.ne').deriv
  have hquot :
      deriv (fun x => deriv phi x / phi x) 0 =
        (secondDeriv phi 0 * phi 0 - deriv phi 0 * deriv phi 0) / phi 0 ^ 2 := by
    have h := hderivDiff.hasDerivAt.div hphiDiff.hasDerivAt hphi0.ne'
    change deriv (deriv phi / phi) 0 =
      (secondDeriv phi 0 * phi 0 - deriv phi 0 * deriv phi 0) / phi 0 ^ 2
    simpa [secondDeriv] using h.deriv
  have hsecond :
      secondDeriv (fun lambda => Real.log (phi lambda)) 0 =
        (secondDeriv phi 0 * phi 0 - deriv phi 0 * deriv phi 0) / phi 0 ^ 2 := by
    unfold secondDeriv
    rw [hlogDerivative.deriv_eq]
    exact hquot
  rw [normalizedCurvature, hfirst, hsecond]
  field_simp [hphi0.ne']
  ring

/-- Pointwise logarithmic derivative convergence controls normalized
curvature and gives the two eventual strict-sign obstructions. -/
theorem logCurvatureObstruction (phi : ℕ → ℝ → ℝ) (a b : ℝ)
    (hsmooth : ∀ n, 0 < phi n 0 ∧ ContDiffAt ℝ 2 (phi n) 0)
    (hfirst : Tendsto
      (fun n => deriv (fun lambda => Real.log (phi n lambda)) 0)
      atTop (𝓝 a))
    (hsecond : Tendsto
      (fun n => secondDeriv (fun lambda => Real.log (phi n lambda)) 0)
      atTop (𝓝 b)) :
    Tendsto (fun n => normalizedCurvature (phi n)) atTop (𝓝 (b + a ^ 2)) ∧
      (0 < b + a ^ 2 →
        ∀ᶠ n in atTop, 0 < normalizedCurvature (phi n)) ∧
      (b + a ^ 2 < 0 →
        ∀ᶠ n in atTop, normalizedCurvature (phi n) < 0) := by
  have hlimitRaw : Tendsto
      (fun n => secondDeriv (fun lambda => Real.log (phi n lambda)) 0 +
        deriv (fun lambda => Real.log (phi n lambda)) 0 ^ 2)
      atTop (𝓝 (b + a ^ 2)) := hsecond.add (hfirst.pow 2)
  have heq :
      (fun n => normalizedCurvature (phi n)) =ᶠ[atTop]
        fun n => secondDeriv (fun lambda => Real.log (phi n lambda)) 0 +
          deriv (fun lambda => Real.log (phi n lambda)) 0 ^ 2 :=
    Filter.Eventually.of_forall fun n =>
      logCurvatureIdentity (phi n) (hsmooth n).1 (hsmooth n).2
  have hlimit : Tendsto (fun n => normalizedCurvature (phi n))
      atTop (𝓝 (b + a ^ 2)) := hlimitRaw.congr' heq.symm
  refine ⟨hlimit, ?_, ?_⟩
  · intro hpos
    exact hlimit.eventually (Ioi_mem_nhds hpos)
  · intro hneg
    exact hlimit.eventually (Iio_mem_nhds hneg)

/-- A twice differentiable convex scalar curve has nonnegative second
derivative at the center of an open interval. -/
theorem convexOn_secondDeriv_nonneg {g : ℝ → ℝ} {eps : ℝ} (heps : 0 < eps)
    (hsmooth : ContDiffOn ℝ 2 g (Ioo (-eps) eps))
    (hconv : ConvexOn ℝ (Ioo (-eps) eps) g) :
    0 ≤ secondDeriv g 0 := by
  have hzero : (0 : ℝ) ∈ Ioo (-eps) eps := by simpa using heps
  have hat : ∀ x ∈ Ioo (-eps) eps, ContDiffAt ℝ 2 g x := fun x hx =>
    hsmooth.contDiffAt (isOpen_Ioo.mem_nhds hx)
  have hmono : MonotoneOn (deriv g) (Ioo (-eps) eps) :=
    hconv.monotoneOn_deriv fun x hx =>
      (hat x hx).differentiableAt (by norm_num)
  have hd : HasDerivAt (deriv g) (secondDeriv g 0) 0 := by
    exact ((hat 0 hzero).derivWithin (m := 1) (by norm_num)).differentiableAt
      one_ne_zero |>.hasDerivAt
  have hacc : AccPt (0 : ℝ) (𝓟 (Ioo (-eps) eps)) :=
    uniqueDiffWithinAt_iff_accPt.mp
      (isOpen_Ioo.uniqueDiffOn.uniqueDiffWithinAt hzero)
  exact hd.hasDerivWithinAt.nonneg_of_monotoneOn hacc hmono

/-- A twice differentiable concave scalar curve has nonpositive second
derivative at the center of an open interval. -/
theorem concaveOn_secondDeriv_nonpos {g : ℝ → ℝ} {eps : ℝ} (heps : 0 < eps)
    (hsmooth : ContDiffOn ℝ 2 g (Ioo (-eps) eps))
    (hconc : ConcaveOn ℝ (Ioo (-eps) eps) g) :
    secondDeriv g 0 ≤ 0 := by
  have hzero : (0 : ℝ) ∈ Ioo (-eps) eps := by simpa using heps
  have hat : ∀ x ∈ Ioo (-eps) eps, ContDiffAt ℝ 2 g x := fun x hx =>
    hsmooth.contDiffAt (isOpen_Ioo.mem_nhds hx)
  have hanti : AntitoneOn (deriv g) (Ioo (-eps) eps) :=
    hconc.antitoneOn_deriv fun x hx =>
      (hat x hx).differentiableAt (by norm_num)
  have hd : HasDerivAt (deriv g) (secondDeriv g 0) 0 := by
    exact ((hat 0 hzero).derivWithin (m := 1) (by norm_num)).differentiableAt
      one_ne_zero |>.hasDerivAt
  have hacc : AccPt (0 : ℝ) (𝓟 (Ioo (-eps) eps)) :=
    uniqueDiffWithinAt_iff_accPt.mp
      (isOpen_Ioo.uniqueDiffOn.uniqueDiffWithinAt hzero)
  exact hd.hasDerivWithinAt.nonpos_of_antitoneOn hacc hanti

/-- Local smoothness plus logarithmic derivative limits rule out the wrong
curvature sign, even when every line has its own radius. -/
theorem typedLogCurvatureContradiction (phi : ℕ → ℝ → ℝ) (a b : ℝ)
    (hsmooth : ∀ n, ∃ eps : ℝ, 0 < eps ∧ 0 < phi n 0 ∧
      ContDiffOn ℝ 2 (phi n) (Ioo (-eps) eps))
    (hfirst : Tendsto
      (fun n => deriv (fun lambda => Real.log (phi n lambda)) 0)
      atTop (𝓝 a))
    (hsecond : Tendsto
      (fun n => secondDeriv (fun lambda => Real.log (phi n lambda)) 0)
      atTop (𝓝 b)) :
    (0 < b + a ^ 2 →
      (∀ n, ∃ eps : ℝ, 0 < eps ∧
        ConcaveOn ℝ (Ioo (-eps) eps) (phi n)) → False) ∧
    (b + a ^ 2 < 0 →
      (∀ n, ∃ eps : ℝ, 0 < eps ∧
        ConvexOn ℝ (Ioo (-eps) eps) (phi n)) → False) := by
  have hsmoothAt : ∀ n, 0 < phi n 0 ∧ ContDiffAt ℝ 2 (phi n) 0 := by
    intro n
    obtain ⟨eps, heps, hpos, hdiff⟩ := hsmooth n
    exact ⟨hpos, hdiff.contDiffAt
      (isOpen_Ioo.mem_nhds (by simpa using heps))⟩
  have hob := logCurvatureObstruction phi a b hsmoothAt hfirst hsecond
  constructor
  · intro hpositive hconc
    obtain ⟨n, hn⟩ := (hob.2.1 hpositive).exists
    obtain ⟨epsSmooth, hepsSmooth, hphi0, hdiff⟩ := hsmooth n
    obtain ⟨epsConc, hepsConc, hconcave⟩ := hconc n
    let eps := min epsSmooth epsConc
    have heps : 0 < eps := lt_min hepsSmooth hepsConc
    have hsubsetSmooth : Ioo (-eps) eps ⊆ Ioo (-epsSmooth) epsSmooth := by
      intro x hx
      exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hx.1,
        hx.2.trans_le (min_le_left _ _)⟩
    have hsubsetConc : Ioo (-eps) eps ⊆ Ioo (-epsConc) epsConc := by
      intro x hx
      exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) hx.1,
        hx.2.trans_le (min_le_right _ _)⟩
    have hsecondPos : 0 < secondDeriv (phi n) 0 := by
      have hmul := mul_pos hn hphi0
      simpa [normalizedCurvature, hphi0.ne'] using hmul
    have hsecondNonpos := concaveOn_secondDeriv_nonpos heps
      (hdiff.mono hsubsetSmooth)
      (hconcave.subset hsubsetConc (convex_Ioo _ _))
    linarith
  · intro hnegative hconv
    obtain ⟨n, hn⟩ := (hob.2.2 hnegative).exists
    obtain ⟨epsSmooth, hepsSmooth, hphi0, hdiff⟩ := hsmooth n
    obtain ⟨epsConv, hepsConv, hconvex⟩ := hconv n
    let eps := min epsSmooth epsConv
    have heps : 0 < eps := lt_min hepsSmooth hepsConv
    have hsubsetSmooth : Ioo (-eps) eps ⊆ Ioo (-epsSmooth) epsSmooth := by
      intro x hx
      exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hx.1,
        hx.2.trans_le (min_le_left _ _)⟩
    have hsubsetConv : Ioo (-eps) eps ⊆ Ioo (-epsConv) epsConv := by
      intro x hx
      exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) hx.1,
        hx.2.trans_le (min_le_right _ _)⟩
    have hsecondNeg : secondDeriv (phi n) 0 < 0 := by
      have hmul := mul_neg_of_neg_of_pos hn hphi0
      simpa [normalizedCurvature, hphi0.ne'] using hmul
    have hsecondNonneg := convexOn_secondDeriv_nonneg heps
      (hdiff.mono hsubsetSmooth)
      (hconvex.subset hsubsetConv (convex_Ioo _ _))
    linarith

/-- A stationary twice differentiable scalar quasi-convex curve cannot have
negative second derivative at the stationary point. -/
theorem quasiconvexSecond {g : ℝ → ℝ} {eps : ℝ} (heps : 0 < eps)
    (hsmooth : ContDiffOn ℝ 2 g (Ioo (-eps) eps))
    (hqcvx : ScalarQCvxOn (Ioo (-eps) eps) g)
    (hstationary : deriv g 0 = 0) :
    0 ≤ secondDeriv g 0 := by
  by_contra hnot
  have hsecond : secondDeriv g 0 < 0 := lt_of_not_ge hnot
  have hsignNhds :
      ∀ᶠ x in 𝓝 (0 : ℝ), sign (deriv g x) = sign (0 - x) := by
    exact eventually_nhdsWithin_sign_eq_of_deriv_neg
      (f := deriv g) hsecond hstationary
  have hsignNE :
      ∀ᶠ x in 𝓝[≠] (0 : ℝ), sign (deriv g x) = sign (0 - x) :=
    hsignNhds.filter_mono nhdsWithin_le_nhds
  have hleftEventually : ∀ᶠ x in 𝓝[<] (0 : ℝ), 0 < deriv g x :=
    deriv_pos_left_of_sign_deriv hsignNE
  have hrightEventually : ∀ᶠ x in 𝓝[>] (0 : ℝ), deriv g x < 0 :=
    deriv_neg_right_of_sign_deriv hsignNE
  obtain ⟨a, ha0, ha⟩ := (nhdsLT_basis (0 : ℝ)).eventually_iff.mp hleftEventually
  obtain ⟨c, hc0, hc⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hrightEventually
  let m : ℝ := min (-a) (min c eps)
  have hm : 0 < m := lt_min (neg_pos.mpr ha0) (lt_min hc0 heps)
  let r : ℝ := m / 2
  have hr : 0 < r := div_pos hm (by norm_num)
  have hrm : r < m := by dsimp [r]; linarith
  have hra : r < -a := hrm.trans_le (min_le_left _ _)
  have hrc : r < c := hrm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hreps : r < eps :=
    hrm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hleftSubset : Icc (-r) 0 ⊆ Ioo (-eps) eps := by
    intro x hx
    exact ⟨(neg_lt_neg hreps).trans_le hx.1, hx.2.trans_lt heps⟩
  have hrightSubset : Icc 0 r ⊆ Ioo (-eps) eps := by
    intro x hx
    exact ⟨(neg_neg_of_pos heps).trans_le hx.1, hx.2.trans_lt hreps⟩
  have hleftDeriv : ∀ x ∈ interior (Icc (-r) 0), 0 < deriv g x := by
    intro x hx
    have hxIoo : x ∈ Ioo (-r) 0 := by
      simpa [interior_Icc, neg_lt_zero.mpr hr] using hx
    exact ha ⟨by linarith [hra, hxIoo.1], hxIoo.2⟩
  have hrightDeriv : ∀ x ∈ interior (Icc 0 r), deriv g x < 0 := by
    intro x hx
    have hxIoo : x ∈ Ioo 0 r := by
      simpa [interior_Icc, hr] using hx
    exact hc ⟨hxIoo.1, hxIoo.2.trans hrc⟩
  have hleftMono : StrictMonoOn g (Icc (-r) 0) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (hsmooth.continuousOn.mono hleftSubset) hleftDeriv
  have hrightAnti : StrictAntiOn g (Icc 0 r) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (hsmooth.continuousOn.mono hrightSubset) hrightDeriv
  have hleftValue : g (-r) < g 0 :=
    hleftMono ⟨le_rfl, (neg_nonpos.mpr hr.le)⟩ ⟨(neg_nonpos.mpr hr.le), le_rfl⟩
      (neg_lt_zero.mpr hr)
  have hrightValue : g r < g 0 :=
    hrightAnti ⟨le_rfl, hr.le⟩ ⟨hr.le, le_rfl⟩ hr
  have hleftMem : -r ∈ Ioo (-eps) eps :=
    hleftSubset ⟨le_rfl, neg_nonpos.mpr hr.le⟩
  have hrightMem : r ∈ Ioo (-eps) eps :=
    hrightSubset ⟨hr.le, le_rfl⟩
  have hmix : (1 / 2 : ℝ) * (-r) + (1 - 1 / 2) * r = 0 := by ring
  have hmixMem :
      (1 / 2 : ℝ) * (-r) + (1 - 1 / 2) * r ∈ Ioo (-eps) eps := by
    rw [hmix]
    simpa using heps
  have hqc := hqcvx (-r) hleftMem r hrightMem (1 / 2)
    (by norm_num) (by norm_num) hmixMem
  rw [hmix] at hqc
  have hmax : max (g (-r)) (g r) < g 0 := max_lt hleftValue hrightValue
  linarith

/-- The exact linearity, continuity and compact-uniform convergence data
needed to correct a limiting stationary direction at every finite index. -/
structure StationarityPackage {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    (aN : ℕ → V →L[ℝ] ℝ) (a : V →L[ℝ] ℝ)
    (bN : ℕ → V → ℝ) (b : V → ℝ) : Prop where
  bN_continuous : ∀ n, Continuous (bN n)
  b_continuous : Continuous b
  aN_compactUniform : ∀ K : Set V, IsCompact K → K.Nonempty →
    TendstoUniformlyOn (fun n x => aN n x) a atTop K
  bN_compactUniform : ∀ K : Set V, IsCompact K → K.Nonempty →
    TendstoUniformlyOn bN b atTop K

/-- Exact stationarity correction.  The proof uses the compact set consisting
of the corrected sequence together with its limit, so finite dimensionality
is not required. -/
theorem stationarityCorrection {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    (aN : ℕ → V →L[ℝ] ℝ) (a : V →L[ℝ] ℝ)
    (bN : ℕ → V → ℝ) (b : V → ℝ)
    (hstat : StationarityPackage aN a bN b)
    (u e : V) (hau : a u = 0) (hbu : b u < 0) (hae : a e ≠ 0) :
    ∃ uN : ℕ → V,
      Tendsto uN atTop (𝓝 u) ∧
      (∀ᶠ n in atTop, aN n (uN n) = 0) ∧
      Tendsto (fun n => bN n (uN n)) atTop (𝓝 (b u)) ∧
      (∀ᶠ n in atTop, bN n (uN n) < 0) := by
  have hAu : Tendsto (fun n => aN n u) atTop (𝓝 (a u)) :=
    (hstat.aN_compactUniform {u} isCompact_singleton (singleton_nonempty u)).tendsto_at
      (mem_singleton u)
  have hAe : Tendsto (fun n => aN n e) atTop (𝓝 (a e)) :=
    (hstat.aN_compactUniform {e} isCompact_singleton (singleton_nonempty e)).tendsto_at
      (mem_singleton e)
  have hAeNe : ∀ᶠ n in atTop, aN n e ≠ 0 := hAe.eventually_ne hae
  let uN : ℕ → V := fun n =>
    if h : aN n e = 0 then u else u - (aN n u / aN n e) • e
  have hratio : Tendsto (fun n => aN n u / aN n e) atTop (𝓝 0) := by
    rw [hau] at hAu
    change Tendsto ((fun n => aN n u) / (fun n => aN n e)) atTop (𝓝 0)
    simpa only [zero_div] using hAu.div hAe hae
  have hbranch : Tendsto
      (fun n => u - (aN n u / aN n e) • e) atTop (𝓝 u) := by
    simpa using tendsto_const_nhds.sub (hratio.smul_const e)
  have huN : Tendsto uN atTop (𝓝 u) := by
    have heq : uN =ᶠ[atTop] fun n => u - (aN n u / aN n e) • e :=
      hAeNe.mono fun n hn => by simp [uN, hn]
    exact hbranch.congr' heq.symm
  have huNstationary : ∀ᶠ n in atTop, aN n (uN n) = 0 := by
    filter_upwards [hAeNe] with n hn
    rw [show uN n = u - (aN n u / aN n e) • e by simp [uN, hn]]
    simp only [map_sub, map_smul]
    change aN n u - (aN n u / aN n e) * aN n e = 0
    rw [div_mul_cancel₀ _ hn, sub_self]
  let K : Set V := insert u (range uN)
  have hKcompact : IsCompact K := huN.isCompact_insert_range
  have hKnonempty : K.Nonempty := ⟨u, mem_insert u (range uN)⟩
  have huNmem : ∀ᶠ n in atTop, uN n ∈ K :=
    Filter.Eventually.of_forall fun n => mem_insert_iff.mpr (Or.inr ⟨n, rfl⟩)
  have huNwithin : Tendsto uN atTop (𝓝[K] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨huN, huNmem⟩
  have hbTendsto : Tendsto (fun n => bN n (uN n)) atTop (𝓝 (b u)) :=
    (hstat.bN_compactUniform K hKcompact hKnonempty).tendsto_comp
      hstat.b_continuous.continuousWithinAt huNwithin
  have hbNeg : ∀ᶠ n in atTop, bN n (uN n) < 0 :=
    hbTendsto.eventually (Iio_mem_nhds hbu)
  exact ⟨uN, huN, huNstationary, hbTendsto, hbNeg⟩

/-- Exact finite-index obstruction obtained by correcting a limiting stationary
direction and applying scalar quasi-convexity on the resulting line. -/
theorem correctedStationaryLineObstruction {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    (gamma : ℕ → V → ℝ → ℝ)
    (aN : ℕ → V →L[ℝ] ℝ) (a : V →L[ℝ] ℝ)
    (bN : ℕ → V → ℝ) (b : V → ℝ)
    (hstat : StationarityPackage aN a bN b)
    (hline : ∀ n v, ∃ eps : ℝ,
      0 < eps ∧
      ContDiffOn ℝ 2 (gamma n v) (Ioo (-eps) eps) ∧
      ScalarQCvxOn (Ioo (-eps) eps) (gamma n v) ∧
      deriv (gamma n v) 0 = aN n v ∧
      secondDeriv (gamma n v) 0 = bN n v)
    (v e : V) (hav : a v = 0) (hbv : b v < 0) (hae : a e ≠ 0) :
    False := by
  obtain ⟨vN, _hvN, hvNstationary, _hbTendsto, hvNnegative⟩ :=
    stationarityCorrection aN a bN b hstat v e hav hbv hae
  obtain ⟨n, hnstationary, hnnegative⟩ :=
    (hvNstationary.and hvNnegative).exists
  obtain ⟨eps, heps, hsmooth, hqcvx, hfirst, hsecond⟩ := hline n (vN n)
  have hcurveStationary : deriv (gamma n (vN n)) 0 = 0 :=
    hfirst.trans hnstationary
  have hcurveNonneg : 0 ≤ secondDeriv (gamma n (vN n)) 0 :=
    quasiconvexSecond heps hsmooth hqcvx hcurveStationary
  rw [hsecond] at hcurveNonneg
  exact (not_lt_of_ge hcurveNonneg) hnnegative

/-- Curvature sign at every point of an arbitrary open convex real domain. -/
theorem lineCurvatureTests (U : Set ℝ) (g : ℝ → ℝ)
    (hUopen : IsOpen U) (_hUconvex : Convex ℝ U)
    (hsmooth : ContDiffOn ℝ 2 g U) :
    (ConcaveOn ℝ U g → ∀ x ∈ U, secondDeriv g x ≤ 0) ∧
    (ConvexOn ℝ U g → ∀ x ∈ U, 0 ≤ secondDeriv g x) := by
  constructor
  · intro hconc x hx
    have hat : ∀ y ∈ U, ContDiffAt ℝ 2 g y := fun y hy =>
      hsmooth.contDiffAt (hUopen.mem_nhds hy)
    have hanti : AntitoneOn (deriv g) U :=
      hconc.antitoneOn_deriv fun y hy =>
        (hat y hy).differentiableAt (by norm_num)
    have hd : HasDerivAt (deriv g) (secondDeriv g x) x := by
      exact ((hat x hx).derivWithin (m := 1) (by norm_num)).differentiableAt
        one_ne_zero |>.hasDerivAt
    have hacc : AccPt x (𝓟 U) :=
      uniqueDiffWithinAt_iff_accPt.mp
        (hUopen.uniqueDiffOn.uniqueDiffWithinAt hx)
    exact hd.hasDerivWithinAt.nonpos_of_antitoneOn hacc hanti
  · intro hconv x hx
    have hat : ∀ y ∈ U, ContDiffAt ℝ 2 g y := fun y hy =>
      hsmooth.contDiffAt (hUopen.mem_nhds hy)
    have hmono : MonotoneOn (deriv g) U :=
      hconv.monotoneOn_deriv fun y hy =>
        (hat y hy).differentiableAt (by norm_num)
    have hd : HasDerivAt (deriv g) (secondDeriv g x) x := by
      exact ((hat x hx).derivWithin (m := 1) (by norm_num)).differentiableAt
        one_ne_zero |>.hasDerivAt
    have hacc : AccPt x (𝓟 U) :=
      uniqueDiffWithinAt_iff_accPt.mp
        (hUopen.uniqueDiffOn.uniqueDiffWithinAt hx)
    exact hd.hasDerivWithinAt.nonneg_of_monotoneOn hacc hmono

/-- A strict limiting second-derivative sign eventually excludes the
incompatible scalar curvature property. -/
theorem lineCurvatureEventual (U : Set ℝ)
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U) (hzero : (0 : ℝ) ∈ U)
    (fseq : ℕ → ℝ → ℝ) (c : ℝ)
    (hsmooth : ∀ n, ContDiffOn ℝ 2 (fseq n) U) :
    ((Tendsto (fun n => secondDeriv (fseq n) 0) atTop (𝓝 c) ∧ 0 < c) →
      ∀ᶠ n in atTop, ¬ ConcaveOn ℝ U (fseq n)) ∧
    ((Tendsto (fun n => secondDeriv (fseq n) 0) atTop (𝓝 c) ∧ c < 0) →
      ∀ᶠ n in atTop, ¬ ConvexOn ℝ U (fseq n)) := by
  constructor
  · rintro ⟨hlim, hc⟩
    have hpos : ∀ᶠ n in atTop, 0 < secondDeriv (fseq n) 0 :=
      hlim.eventually (Ioi_mem_nhds hc)
    filter_upwards [hpos] with n hn hconc
    have hnonpos := (lineCurvatureTests U (fseq n) hUopen hUconvex
      (hsmooth n)).1 hconc 0 hzero
    exact (not_lt_of_ge hnonpos) hn
  · rintro ⟨hlim, hc⟩
    have hneg : ∀ᶠ n in atTop, secondDeriv (fseq n) 0 < 0 :=
      hlim.eventually (Iio_mem_nhds hc)
    filter_upwards [hneg] with n hn hconv
    have hnonneg := (lineCurvatureTests U (fseq n) hUopen hUconvex
      (hsmooth n)).2 hconv 0 hzero
    exact (not_lt_of_ge hnonneg) hn

end ConditionalEntropy
