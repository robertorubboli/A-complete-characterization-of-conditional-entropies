import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Integral

/-!
# Compactified parameters and finite signed integration

This module supplies the endpoint-aware parameter carrier used by the Renyi
family and a small, explicit API for finite signed measures.  Signed integrals
are defined from the canonical Jordan decomposition, so no convention about
the sign of a measure is hidden in coercions.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ConditionalEntropy

/-! ## The compactified nonnegative parameter -/

/-- The ordered one-point compactification `[0, +infinity]`. -/
abbrev Param := WithTop NNReal

/-- Embed a real parameter in `Param`; negative inputs are sent to zero. -/
def finiteParam (r : ℝ) : Param := ENNReal.ofReal r

@[simp] theorem finiteParam_zero : finiteParam 0 = 0 := by
  exact ENNReal.ofReal_zero

@[simp] theorem finiteParam_one : finiteParam 1 = 1 := by
  exact ENNReal.ofReal_one

theorem finiteParam_ne_top (r : ℝ) : finiteParam r ≠ (⊤ : Param) := by
  exact ENNReal.ofReal_ne_top

theorem finiteParam_eq_zero_iff {r : ℝ} : finiteParam r = 0 ↔ r ≤ 0 := by
  exact ENNReal.ofReal_eq_zero

theorem finiteParam_injectiveOn_nonneg :
    Set.InjOn finiteParam (Set.Ici (0 : ℝ)) := by
  intro r hr s hs h
  exact (ENNReal.ofReal_eq_ofReal_iff hr hs).mp h

/-- Extract the real value of a finite parameter. -/
def paramToReal (a : Param) (_h : a ≠ ⊤) : ℝ := ENNReal.toReal a

@[simp] theorem paramToReal_finiteParam {r : ℝ} (hr : 0 ≤ r) :
    paramToReal (finiteParam r) (finiteParam_ne_top r) = r := by
  exact ENNReal.toReal_ofReal_eq_iff.mpr hr

theorem finiteParam_paramToReal (a : Param) (h : a ≠ ⊤) :
    finiteParam (paramToReal a h) = a := by
  exact ENNReal.ofReal_toReal h

/-- The singular coefficient `a / (1-a)`, with its manuscript endpoint values. -/
def singularWeight (a : Param) : ℝ :=
  if htop : a = ⊤ then -1
  else
    let r := paramToReal a htop
    if r = 1 then 0 else r / (1 - r)

@[simp] theorem singularWeight_top : singularWeight (⊤ : Param) = -1 := by
  simp [singularWeight]

@[simp] theorem singularWeight_zero : singularWeight (0 : Param) = 0 := by
  rw [singularWeight]
  simp only [WithTop.zero_ne_top, ↓reduceDIte]
  change (if (0 : ℝ) = 1 then 0 else 0 / (1 - 0)) = 0
  norm_num

@[simp] theorem singularWeight_one : singularWeight (1 : Param) = 0 := by
  rw [singularWeight]
  simp only [WithTop.one_ne_top, ↓reduceDIte]
  change (if (1 : ℝ) = 1 then 0 else 1 / (1 - 1)) = 0
  norm_num

theorem singularWeight_finite {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≠ 1) :
    singularWeight (finiteParam r) = r / (1 - r) := by
  simp [singularWeight, finiteParam_ne_top, paramToReal_finiteParam hr, hr1]

/-- The singular coefficient is strictly positive at every finite order
strictly between zero and one. -/
theorem singularWeight_pos_of_Ioo {a : Param}
    (ha : a ∈ Set.Ioo (0 : Param) 1) : 0 < singularWeight a := by
  have hatop : a ≠ ⊤ := ne_top_of_lt ha.2
  have ha0 : a ≠ 0 := ne_of_gt ha.1
  have hrpos : 0 < ENNReal.toReal a := ENNReal.toReal_pos ha0 hatop
  have hrlt : ENNReal.toReal a < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hatop ENNReal.one_ne_top).mpr ha.2
  rw [singularWeight, dif_neg hatop]
  change (if ENNReal.toReal a = 1 then 0
    else ENNReal.toReal a / (1 - ENNReal.toReal a)) > 0
  rw [if_neg (ne_of_lt hrlt)]
  exact div_pos hrpos (sub_pos.mpr hrlt)

/-- The singular coefficient is strictly negative above order one,
including at the compactified endpoint. -/
theorem singularWeight_neg_of_one_lt {a : Param} (ha : 1 < a) :
    singularWeight a < 0 := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe q =>
      have hq : (1 : ℝ) < (q : ℝ) := by exact_mod_cast ha
      have hq0 : 0 ≤ (q : ℝ) := q.2
      have hq1 : (q : ℝ) ≠ 1 := ne_of_gt hq
      rw [← show finiteParam (q : ℝ) = (q : Param) by simp [finiteParam],
        singularWeight_finite hq0 hq1]
      exact div_neg_of_pos_of_neg (lt_trans zero_lt_one hq) (sub_neg.mpr hq)

/-! ## Positive and signed measures -/

/-- Expose the underlying measure of a bundled probability measure. -/
def probMeasure (τ : ProbabilityMeasure Param) : Measure Param := τ

/-- Expose the underlying measure of a bundled finite measure. -/
def finiteMeasure (σ : FiniteMeasure Param) : Measure Param := σ

/-- The mass of an atom of a probability measure. -/
def atom (τ : ProbabilityMeasure Param) (a : Param) : ENNReal :=
  probMeasure τ {a}

/-- Push a probability measure forward along an almost-everywhere measurable map. -/
def probMap (τ : ProbabilityMeasure Param) (T : Param → Param)
    (hT : AEMeasurable T (probMeasure τ)) : ProbabilityMeasure Param :=
  τ.map hT

/-- The total pushforward constructor for a bundled finite measure. -/
def finiteMap (σ : FiniteMeasure Param) (T : Param → Param) : FiniteMeasure Param :=
  σ.map T

/-- A convex mixture of two probability measures. -/
def probMix (τ ρ : ProbabilityMeasure Param) (ε : ℝ)
    (hε : 0 ≤ ε ∧ ε ≤ 1) : ProbabilityMeasure Param :=
  ⟨ENNReal.ofReal (1 - ε) • probMeasure τ + ENNReal.ofReal ε • probMeasure ρ, by
    have h1 : 0 ≤ 1 - ε := sub_nonneg.mpr hε.2
    have hτ : probMeasure τ Set.univ = 1 := by simp [probMeasure]
    have hρ : probMeasure ρ Set.univ = 1 := by simp [probMeasure]
    apply isProbabilityMeasure_iff.mpr
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, hτ, hρ, mul_one]
    rw [← ENNReal.ofReal_add h1 hε.1, sub_add_cancel, ENNReal.ofReal_one]⟩

/-- Scale a finite positive measure by a nonnegative real. -/
def finiteScale (c : ℝ) (_hc : 0 ≤ c) (σ : FiniteMeasure Param) : FiniteMeasure Param :=
  ⟨ENNReal.ofReal c • finiteMeasure σ, by
    constructor
    have hσ : finiteMeasure σ Set.univ < (⊤ : ENNReal) := by
      change (σ : Measure Param) Set.univ < (⊤ : ENNReal)
      exact measure_lt_top _ _
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hσ⟩

/-- A bundled point-mass probability measure. -/
def diracProb (a : Param) : ProbabilityMeasure Param :=
  diracProba a

/-- The raw point-mass measure. -/
def diracRaw (a : Param) : Measure Param := probMeasure (diracProb a)

@[simp] theorem diracRaw_apply (a : Param) {s : Set Param} (_hs : MeasurableSet s) :
    diracRaw a s = s.indicator 1 a := by
  simp [diracRaw, diracProb, probMeasure]

/-- Regard a finite positive measure as a signed measure. -/
def signedLift {E : Type*} [MeasurableSpace E] (σ : FiniteMeasure E) : SignedMeasure E :=
  ((σ : Measure E)).toSignedMeasure

/-- The Jordan decomposition canonically associated with a positive measure. -/
def positiveJordan {E : Type*} [MeasurableSpace E]
    (σ : FiniteMeasure E) : JordanDecomposition E where
  posPart := σ
  negPart := 0
  mutuallySingular := Measure.MutuallySingular.zero_right

/-- The positive Jordan component of a signed measure. -/
def signedPos {E : Type*} [MeasurableSpace E] (μ : SignedMeasure E) : Measure E :=
  μ.toJordanDecomposition.posPart

/-- The negative Jordan component of a signed measure. -/
def signedNeg {E : Type*} [MeasurableSpace E] (μ : SignedMeasure E) : Measure E :=
  μ.toJordanDecomposition.negPart

/-- The total variation obtained from the Jordan decomposition. -/
def signedTV {E : Type*} [MeasurableSpace E] (μ : SignedMeasure E) : Measure E :=
  μ.totalVariation

theorem signedTV_eq_add {E : Type*} [MeasurableSpace E] (μ : SignedMeasure E) :
    signedTV μ = signedPos μ + signedNeg μ := rfl

theorem signedLift_eq_positiveJordan {E : Type*} [MeasurableSpace E]
    (σ : FiniteMeasure E) : signedLift σ = (positiveJordan σ).toSignedMeasure := by
  simp [signedLift, positiveJordan, JordanDecomposition.toSignedMeasure]

@[simp] theorem signedPos_signedLift {E : Type*} [MeasurableSpace E]
    (σ : FiniteMeasure E) : signedPos (signedLift σ) = (σ : Measure E) := by
  rw [signedLift_eq_positiveJordan]
  simp [signedPos, positiveJordan]

@[simp] theorem signedNeg_signedLift {E : Type*} [MeasurableSpace E]
    (σ : FiniteMeasure E) : signedNeg (signedLift σ) = 0 := by
  rw [signedLift_eq_positiveJordan]
  simp [signedNeg, positiveJordan]

@[simp] theorem signedTV_signedLift {E : Type*} [MeasurableSpace E]
    (σ : FiniteMeasure E) : signedTV (signedLift σ) = (σ : Measure E) := by
  rw [signedTV_eq_add, signedPos_signedLift, signedNeg_signedLift, add_zero]

instance signedPos_isFiniteMeasure {E : Type*} [MeasurableSpace E] (μ : SignedMeasure E) :
    IsFiniteMeasure (signedPos μ) := by
  unfold signedPos
  infer_instance

instance signedNeg_isFiniteMeasure {E : Type*} [MeasurableSpace E] (μ : SignedMeasure E) :
    IsFiniteMeasure (signedNeg μ) := by
  unfold signedNeg
  infer_instance

instance signedTV_isFiniteMeasure {E : Type*} [MeasurableSpace E] (μ : SignedMeasure E) :
    IsFiniteMeasure (signedTV μ) := by
  rw [signedTV_eq_add]
  infer_instance

/-- The canonical real integral against a finite signed measure. -/
def signedIntegral {E : Type*} [MeasurableSpace E]
    (μ : SignedMeasure E) (f : E → ℝ) : ℝ :=
  ∫ x, f x ∂signedPos μ - ∫ x, f x ∂signedNeg μ

@[simp] theorem signedIntegral_zero_fun {E : Type*} [MeasurableSpace E]
    (μ : SignedMeasure E) : signedIntegral μ (fun _ => 0) = 0 := by
  simp [signedIntegral]

@[simp] theorem signedIntegral_signedLift {E : Type*} [MeasurableSpace E]
    (σ : FiniteMeasure E) (f : E → ℝ) :
    signedIntegral (signedLift σ) f = ∫ x, f x ∂(σ : Measure E) := by
  simp [signedIntegral]

theorem signedIntegral_congr_ae {E : Type*} [MeasurableSpace E]
    (μ : SignedMeasure E) {f g : E → ℝ}
    (h : f =ᵐ[signedTV μ] g) : signedIntegral μ f = signedIntegral μ g := by
  have hparts :=
    (SignedMeasure.totalVariation_absolutelyContinuous_iff μ (signedTV μ)).mp
      (Measure.AbsolutelyContinuous.rfl)
  have hpos : f =ᵐ[signedPos μ] g := hparts.1.ae_le h
  have hneg : f =ᵐ[signedNeg μ] g := hparts.2.ae_le h
  simp only [signedIntegral]
  rw [integral_congr_ae hpos, integral_congr_ae hneg]

theorem signedIntegral_add {E : Type*} [MeasurableSpace E]
    (μ : SignedMeasure E) {f g : E → ℝ}
    (hfpos : Integrable f (signedPos μ)) (hfneg : Integrable f (signedNeg μ))
    (hgpos : Integrable g (signedPos μ)) (hgneg : Integrable g (signedNeg μ)) :
    signedIntegral μ (fun x => f x + g x) = signedIntegral μ f + signedIntegral μ g := by
  simp only [signedIntegral]
  rw [integral_add hfpos hgpos, integral_add hfneg hgneg]
  ring_nf

theorem signedIntegral_smul {E : Type*} [MeasurableSpace E]
    (μ : SignedMeasure E) (c : ℝ) (f : E → ℝ) :
    signedIntegral μ (fun x => c * f x) = c * signedIntegral μ f := by
  simp [signedIntegral, integral_const_mul]
  ring_nf

theorem signedIntegral_finset_sum {E ι : Type*} [MeasurableSpace E]
    (μ : SignedMeasure E) (s : Finset ι) (f : ι → E → ℝ)
    (hpos : ∀ i ∈ s, Integrable (f i) (signedPos μ))
    (hneg : ∀ i ∈ s, Integrable (f i) (signedNeg μ)) :
    signedIntegral μ (fun x => ∑ i ∈ s, f i x) =
      ∑ i ∈ s, signedIntegral μ (f i) := by
  classical
  simp only [signedIntegral]
  rw [integral_finsetSum _ hpos, integral_finsetSum _ hneg]
  rw [Finset.sum_sub_distrib]

/-- A signed measure is one-signed when one Jordan component vanishes. -/
def OneSigned {E : Type*} [MeasurableSpace E] (μ : SignedMeasure E) : Prop :=
  signedPos μ = 0 ∨ signedNeg μ = 0

/-- The support used for a signed measure is the support of its total variation. -/
def suppSigned {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (μ : SignedMeasure E) : Set E :=
  (signedTV μ).support

/-! ## Finite atomic discretizations -/

/-- The signed measure represented by finitely many locations and real weights. -/
def atomicSignedMeasure {E ι : Type*} [MeasurableSpace E]
    (s : Finset ι) (point : ι → E) (weight : ι → ℝ) : SignedMeasure E :=
  ∑ i ∈ s, VectorMeasure.dirac (point i) (weight i)

/-- The vector-measure integral specialized to real signed measures. -/
def vectorSignedIntegral {E : Type*} [MeasurableSpace E]
    (μ : SignedMeasure E) (f : E → ℝ) : ℝ :=
  ∫ᵛ x, f x ∂<•μ

theorem vectorSignedIntegral_atomic {E ι : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] (s : Finset ι) (point : ι → E) (weight : ι → ℝ)
    (f : E → ℝ) :
    vectorSignedIntegral (atomicSignedMeasure s point weight) f =
      ∑ i ∈ s, f (point i) * weight i := by
  classical
  have hdirac : ∀ i ∈ s, (VectorMeasure.dirac (point i) (weight i)).Integrable f := by
    intro i _
    change Integrable f (VectorMeasure.dirac (point i) (weight i)).variation
    simp only [VectorMeasure.variation_dirac]
    exact (integrable_dirac (a := point i) (f := f) (by simp)).smul_measure (by simp)
  unfold vectorSignedIntegral atomicSignedMeasure
  rw [VectorMeasure.integral_finsetSum_vectorMeasure hdirac]
  simp only [VectorMeasure.integral_dirac]
  apply Finset.sum_congr rfl
  intro i _
  change weight i * f (point i) = f (point i) * weight i
  exact mul_comm _ _

/-! ## Positive-base real-power calculus -/

/-- The second ordinary derivative, as a total function. -/
def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ := deriv (deriv f) x

theorem hasDerivAt_rpow_of_pos (β y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => z ^ β) (β * y ^ (β - 1)) y :=
  Real.hasDerivAt_rpow_const (Or.inl hy.ne')

theorem secondDeriv_rpow_of_pos (β y : ℝ) (_hy : 0 < y) :
    secondDeriv (fun z : ℝ => z ^ β) y = β * (β - 1) * y ^ (β - 2) := by
  unfold secondDeriv
  rw [Real.deriv_rpow_const']
  simp only [deriv_const_mul_field, Real.deriv_rpow_const]
  ring_nf

theorem contDiffOn_rpow_Ioi (β : ℝ) :
    ContDiffOn ℝ 2 (fun y : ℝ => y ^ β) (Set.Ioi 0) := by
  intro y hy
  exact (Real.contDiffAt_rpow_const_of_ne hy.ne').contDiffWithinAt

theorem realRpowCalculus (β : ℝ) :
    ContDiffOn ℝ 2 (fun y : ℝ => y ^ β) (Set.Ioi 0) ∧
      (∀ y ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun z : ℝ => z ^ β) (β * y ^ (β - 1)) y) ∧
      (∀ y ∈ Set.Ioi (0 : ℝ),
        secondDeriv (fun z : ℝ => z ^ β) y = β * (β - 1) * y ^ (β - 2)) ∧
      (0 ≤ β → MonotoneOn (fun y : ℝ => y ^ β) (Set.Ioi 0)) ∧
      (β ≤ 0 → AntitoneOn (fun y : ℝ => y ^ β) (Set.Ioi 0)) ∧
      (0 < β → StrictMonoOn (fun y : ℝ => y ^ β) (Set.Ioi 0)) ∧
      (β < 0 → StrictAntiOn (fun y : ℝ => y ^ β) (Set.Ioi 0)) := by
  refine ⟨contDiffOn_rpow_Ioi β, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact hasDerivAt_rpow_of_pos β y hy
  · intro y hy
    exact secondDeriv_rpow_of_pos β y hy
  · intro hβ
    exact (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hβ).mono Set.Ioi_subset_Ici_self
  · exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
  · intro hβ
    exact (Real.strictMonoOn_rpow_Ici_of_exponent_pos hβ).mono Set.Ioi_subset_Ici_self
  · exact Real.strictAntiOn_rpow_Ioi_of_exponent_neg

/-! ## Differentiation under a finite signed integral -/

/-- A local dominated-derivative rule for the Jordan signed integral. -/
theorem hasDerivAt_signedIntegral_of_dominated_loc
    {E : Type*} [MeasurableSpace E]
    (μ : SignedMeasure E) {F F' : ℝ → E → ℝ} {x₀ : ℝ} {s : Set ℝ}
    {bound : E → ℝ}
    (hs : s ∈ 𝓝 x₀)
    (hFmeas : ∀ᶠ x in 𝓝 x₀, StronglyMeasurable (F x))
    (hFintPos : Integrable (F x₀) (signedPos μ))
    (hFintNeg : Integrable (F x₀) (signedNeg μ))
    (hF'meas : StronglyMeasurable (F' x₀))
    (hbound : ∀ a x, x ∈ s → ‖F' x a‖ ≤ bound a)
    (hboundPos : Integrable bound (signedPos μ))
    (hboundNeg : Integrable bound (signedNeg μ))
    (hdiff : ∀ a x, x ∈ s → HasDerivAt (fun z => F z a) (F' x a) x) :
    HasDerivAt (fun x => signedIntegral μ (F x))
      (signedIntegral μ (F' x₀)) x₀ := by
  have hpos := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := signedPos μ) hs
    (hFmeas.mono fun _ h => h.aestronglyMeasurable) hFintPos
    hF'meas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun a x hx => hbound a x hx) hboundPos
    (Filter.Eventually.of_forall fun a x hx => hdiff a x hx)
  have hneg := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := signedNeg μ) hs
    (hFmeas.mono fun _ h => h.aestronglyMeasurable) hFintNeg
    hF'meas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun a x hx => hbound a x hx) hboundNeg
    (Filter.Eventually.of_forall fun a x hx => hdiff a x hx)
  convert hpos.2.sub hneg.2 using 1 <;> rfl

/-- Apply dominated differentiation twice to three successive kernels. -/
theorem signedIntegral_differentiate_twice
    {E : Type*} [MeasurableSpace E]
    (μ : SignedMeasure E) {k₀ k₁ k₂ : ℝ → E → ℝ} {x₀ : ℝ} {s : Set ℝ}
    {bound₀ bound₁ : E → ℝ}
    (hs : s ∈ 𝓝 x₀)
    (hk₀meas : ∀ᶠ x in 𝓝 x₀, StronglyMeasurable (k₀ x))
    (hk₁meas : ∀ᶠ x in 𝓝 x₀, StronglyMeasurable (k₁ x))
    (hk₀intPos : Integrable (k₀ x₀) (signedPos μ))
    (hk₀intNeg : Integrable (k₀ x₀) (signedNeg μ))
    (hk₁intPos : Integrable (k₁ x₀) (signedPos μ))
    (hk₁intNeg : Integrable (k₁ x₀) (signedNeg μ))
    (hk₁strong : StronglyMeasurable (k₁ x₀))
    (hk₂strong : StronglyMeasurable (k₂ x₀))
    (hbound₀ : ∀ a x, x ∈ s → ‖k₁ x a‖ ≤ bound₀ a)
    (hbound₁ : ∀ a x, x ∈ s → ‖k₂ x a‖ ≤ bound₁ a)
    (hbound₀Pos : Integrable bound₀ (signedPos μ))
    (hbound₀Neg : Integrable bound₀ (signedNeg μ))
    (hbound₁Pos : Integrable bound₁ (signedPos μ))
    (hbound₁Neg : Integrable bound₁ (signedNeg μ))
    (hderiv₀ : ∀ a x, x ∈ s → HasDerivAt (fun z => k₀ z a) (k₁ x a) x)
    (hderiv₁ : ∀ a x, x ∈ s → HasDerivAt (fun z => k₁ z a) (k₂ x a) x) :
    HasDerivAt (fun x => signedIntegral μ (k₀ x)) (signedIntegral μ (k₁ x₀)) x₀ ∧
      HasDerivAt (fun x => signedIntegral μ (k₁ x)) (signedIntegral μ (k₂ x₀)) x₀ := by
  constructor
  · exact hasDerivAt_signedIntegral_of_dominated_loc μ hs hk₀meas
      hk₀intPos hk₀intNeg hk₁strong hbound₀ hbound₀Pos hbound₀Neg hderiv₀
  · exact hasDerivAt_signedIntegral_of_dominated_loc μ hs hk₁meas
      hk₁intPos hk₁intNeg hk₂strong hbound₁ hbound₁Pos hbound₁Neg hderiv₁

end ConditionalEntropy
