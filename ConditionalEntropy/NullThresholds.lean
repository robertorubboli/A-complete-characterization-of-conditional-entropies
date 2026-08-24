import ConditionalEntropy.Moments
import ConditionalEntropy.SignedWitnesses
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Order.IsLUB

/-!
# Null thresholds and strict support inequalities

This module supplies null atoms in the finite order coordinate and the
support lemmas used by the necessity witnesses.  Real thresholds are always
embedded by `finiteParam`; no real number is compared directly with `Param`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators

namespace ConditionalEntropy

/-! ## Countability and null points -/

/-- The atoms of an s-finite measure form a countable set. -/
theorem countable_nonzero_atoms (nu : Measure Param) [SFinite nu] :
    Set.Countable {a : Param | nu ({a} : Set Param) ≠ 0} := by
  have h := Measure.countable_meas_level_set_pos
    (μ := nu) (g := id) measurable_id
  have heq : {t : Param | 0 < nu {a : Param | id a = t}} =
      {a : Param | nu ({a} : Set Param) ≠ 0} := by
    ext t
    simp only [id_eq, mem_setOf_eq, pos_iff_ne_zero]
    have hset : {a : Param | a = t} = ({t} : Set Param) := by
      ext a
      simp [eq_comm]
    rw [hset]
  rw [← heq]
  exact h

/-- Nonnegative real parameters whose embedded points are atoms. -/
def realAtomSet (nu : Measure Param) : Set ℝ :=
  {r | 0 ≤ r ∧ nu ({finiteParam r} : Set Param) ≠ 0}

/-- The nonnegative real pullback of the atom set is countable. -/
theorem countable_realAtomSet (nu : Measure Param) [SFinite nu] :
    (realAtomSet nu).Countable := by
  let A : Set Param := {a | nu ({a} : Set Param) ≠ 0}
  have hA : A.Countable := countable_nonzero_atoms nu
  have hmaps : MapsTo finiteParam (realAtomSet nu) A := by
    intro r hr
    exact hr.2
  have hinj : InjOn finiteParam (realAtomSet nu) := by
    intro r hr s hs hrs
    exact finiteParam_injectiveOn_nonneg hr.1 hs.1 hrs
  exact hmaps.countable_of_injOn hinj hA

/-- Every nonempty open subset of `Param` contains a strictly positive finite
parameter. -/
theorem exists_pos_finiteParam_mem_open {U : Set Param}
    (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ r : ℝ, 0 < r ∧ finiteParam r ∈ U := by
  obtain ⟨x, hxU⟩ := hUne
  by_cases hxtop : x = (⊤ : Param)
  · subst x
    have hevent : ∀ᶠ r : ℝ in atTop, finiteParam r ∈ U :=
      ENNReal.tendsto_ofReal_atTop.eventually (hU.mem_nhds hxU)
    have hpos : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
    exact (hevent.and hpos).exists.imp fun r hr => ⟨hr.2, hr.1⟩
  · let r := ENNReal.toReal x
    by_cases hrpos : 0 < r
    · exact ⟨r, hrpos, by
        rw [show finiteParam r = x by
          exact finiteParam_paramToReal x hxtop]
        exact hxU⟩
    · have hrzero : r = 0 := by
        exact le_antisymm (not_lt.mp hrpos) (ENNReal.toReal_nonneg)
      have hxzero : x = 0 := by
        change paramToReal x hxtop = 0 at hrzero
        rw [← finiteParam_paramToReal x hxtop, hrzero, finiteParam_zero]
      subst x
      have hnhds : U ∈ 𝓝 (0 : Param) := hU.mem_nhds hxU
      obtain ⟨b, hb, hbU⟩ := ENNReal.nhds_zero_basis.mem_iff.mp hnhds
      obtain ⟨y, hy0, hyb⟩ := exists_between hb
      have hytop : y ≠ (⊤ : Param) := ne_top_of_lt (hyb.trans_le le_top)
      let q := ENNReal.toReal y
      have hqpos : 0 < q := ENNReal.toReal_pos hy0.ne' hytop
      refine ⟨q, hqpos, hbU ?_⟩
      rw [show finiteParam q = y by
        exact finiteParam_paramToReal y hytop]
      exact hyb

/-- Every nonempty open parameter set contains a null singleton. -/
theorem exists_null_atom_mem_open (nu : Measure Param) [IsFiniteMeasure nu]
    {U : Set Param} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ a ∈ U, nu ({a} : Set Param) = 0 := by
  let B := realAtomSet nu
  have hB : B.Countable := countable_realAtomSet nu
  have hDense : Dense Bᶜ := hB.dense_compl ℝ
  let W : Set ℝ := finiteParam ⁻¹' U ∩ Ioi 0
  have hWopen : IsOpen W :=
    (hU.preimage ENNReal.continuous_ofReal).inter isOpen_Ioi
  have hWne : W.Nonempty := by
    obtain ⟨r, hr, hrU⟩ := exists_pos_finiteParam_mem_open hU hUne
    exact ⟨r, hrU, hr⟩
  obtain ⟨r, hrB, hrW⟩ := hDense.exists_mem_open hWopen hWne
  refine ⟨finiteParam r, hrW.1, ?_⟩
  by_contra hratom
  exact hrB ⟨hrW.2.le, hratom⟩

/-! ## Tail and separation thresholds -/

/-- A support point makes every open neighbourhood have positive measure. -/
theorem measure_pos_of_mem_support_open {nu : Measure Param} {x : Param}
    (hx : x ∈ suppMeasure nu) {U : Set Param}
    (hU : IsOpen U) (hxU : x ∈ U) :
    0 < nu U := by
  rw [suppMeasure, Measure.support_eq_forall_isOpen] at hx
  exact hx U hxU hU

/-- A positive upper tail admits a strictly larger finite null threshold with
positive remaining tail.  The chosen threshold is stronger than the
manuscript's `s < r`: it satisfies `max s 0 < r`. -/
theorem exists_null_tail_threshold (nu : Measure Param) [IsFiniteMeasure nu]
    (s : ℝ) (htail : 0 < nu (Ioi (finiteParam s))) :
    ∃ r : ℝ, max s 0 < r ∧
      nu ({finiteParam r} : Set Param) = 0 ∧
      0 < nu (Ioi (finiteParam r)) := by
  obtain ⟨x, hxs, hxsupp⟩ :=
    Measure.nonempty_inter_support_of_pos htail
  have hmaxEq : finiteParam (max s 0) = finiteParam s := by
    by_cases hs : 0 ≤ s
    · rw [max_eq_left hs]
    · rw [max_eq_right (le_of_not_ge hs), finiteParam_eq_zero_iff.mpr
          (le_of_not_ge hs), finiteParam_zero]
  have hlowx : finiteParam (max s 0) < x := by
    rw [hmaxEq]
    exact hxs
  have hopen : IsOpen (Ioo (finiteParam (max s 0)) x) := isOpen_Ioo
  have hne : (Ioo (finiteParam (max s 0)) x).Nonempty := nonempty_Ioo.mpr hlowx
  obtain ⟨a, ha, hnull⟩ := exists_null_atom_mem_open nu hopen hne
  have hatop : a ≠ (⊤ : Param) := ne_top_of_lt (ha.2.trans_le le_top)
  let r := ENNReal.toReal a
  have hraFinite : finiteParam r = a := finiteParam_paramToReal a hatop
  have hra : ENNReal.ofReal r = a := hraFinite
  have hmaxr : max s 0 < r := by
    have hmax0 : 0 ≤ max s 0 := le_max_right _ _
    rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg hmax0, hra]
    exact ha.1
  refine ⟨r, hmaxr, ?_, ?_⟩
  · simpa only [hraFinite] using hnull
  · apply measure_pos_of_mem_support_open hxsupp isOpen_Ioi
    change finiteParam r < x
    rw [hraFinite]
    exact ha.2

/-- Two finite support parameters can be separated by a finite null point. -/
theorem exists_null_between_support (nu : Measure Param) [IsFiniteMeasure nu]
    {a1 a2 : ℝ} (ha1 : 0 ≤ a1) (ha12 : a1 < a2)
    (_hsupp1 : finiteParam a1 ∈ suppMeasure nu)
    (_hsupp2 : finiteParam a2 ∈ suppMeasure nu) :
    ∃ r : ℝ, a1 < r ∧ r < a2 ∧
      nu ({finiteParam r} : Set Param) = 0 := by
  have hparam : finiteParam a1 < finiteParam a2 := by
    change ENNReal.ofReal a1 < ENNReal.ofReal a2
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha1]
    exact ha12
  obtain ⟨a, ha, hnull⟩ := exists_null_atom_mem_open nu isOpen_Ioo
    (nonempty_Ioo.mpr hparam)
  have hatop : a ≠ (⊤ : Param) := ne_top_of_lt (ha.2.trans_le le_top)
  let r := ENNReal.toReal a
  have hraFinite : finiteParam r = a := finiteParam_paramToReal a hatop
  have hra : ENNReal.ofReal r = a := hraFinite
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  refine ⟨r, ?_, ?_, ?_⟩
  · rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha1, hra]
    exact ha.1
  · rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr0, hra]
    exact ha.2
  · simpa only [hraFinite] using hnull

/-- Null atoms contain a strictly increasing sequence from below converging to
the Shannon parameter. -/
theorem exists_null_seq_below_one (nu : Measure Param) [IsFiniteMeasure nu] :
    ∃ r : ℕ → ℝ, StrictMono r ∧
      (∀ n, 0 < r n ∧ r n < 1 ∧
        nu ({finiteParam (r n)} : Set Param) = 0) ∧
      Tendsto r atTop (𝓝 1) := by
  let B := realAtomSet nu
  have hDense : Dense Bᶜ := (countable_realAtomSet nu).dense_compl ℝ
  obtain ⟨r, hrmono, hrmem, hrtendsto⟩ :=
    hDense.exists_seq_strictMono_tendsto_of_lt (show (0 : ℝ) < 1 by norm_num)
  refine ⟨r, hrmono, ?_, hrtendsto⟩
  intro n
  have hrI := (hrmem n).1
  have hrB := (hrmem n).2
  refine ⟨hrI.1, hrI.2, ?_⟩
  by_contra hatom
  exact hrB ⟨hrI.1.le, hatom⟩

/-- Null atoms contain a strictly decreasing sequence from above converging to
the Shannon parameter. -/
theorem exists_null_seq_above_one (nu : Measure Param) [IsFiniteMeasure nu] :
    ∃ s : ℕ → ℝ, StrictAnti s ∧
      (∀ n, 1 < s n ∧ nu ({finiteParam (s n)} : Set Param) = 0) ∧
      Tendsto s atTop (𝓝 1) := by
  let B := realAtomSet nu
  have hDense : Dense Bᶜ := (countable_realAtomSet nu).dense_compl ℝ
  obtain ⟨s, hsanti, hsmem, hstendsto⟩ :=
    hDense.exists_seq_strictAnti_tendsto_of_lt (show (1 : ℝ) < 2 by norm_num)
  refine ⟨s, hsanti, ?_, hstendsto⟩
  intro n
  have hsI := (hsmem n).1
  have hsB := (hsmem n).2
  refine ⟨hsI.1, ?_⟩
  by_contra hatom
  exact hsB ⟨by linarith [hsI.1], hatom⟩

/-- Literal null-threshold package from the manuscript. -/
theorem nullThresholds (nu : Measure Param) [IsFiniteMeasure nu] :
    Set.Countable {a : Param | nu ({a} : Set Param) ≠ 0} ∧
      (∀ U : Set Param, IsOpen U → U.Nonempty →
        ∃ a ∈ U, nu ({a} : Set Param) = 0) ∧
      (∀ s : ℝ, 0 < nu (Ioi (finiteParam s)) →
        ∃ r : ℝ, s < r ∧ nu ({finiteParam r} : Set Param) = 0 ∧
          0 < nu (Ioi (finiteParam r))) ∧
      (∀ a1 a2 : ℝ, 0 ≤ a1 → a1 < a2 →
        finiteParam a1 ∈ suppMeasure nu →
        finiteParam a2 ∈ suppMeasure nu →
        ∃ r : ℝ, a1 < r ∧ r < a2 ∧
          nu ({finiteParam r} : Set Param) = 0) ∧
      (∃ r : ℕ → ℝ, StrictMono r ∧
        (∀ n, 0 < r n ∧ r n < 1 ∧
          nu ({finiteParam (r n)} : Set Param) = 0) ∧
        Tendsto r atTop (𝓝 1)) ∧
      (∃ s : ℕ → ℝ, StrictAnti s ∧
        (∀ n, 1 < s n ∧ nu ({finiteParam (s n)} : Set Param) = 0) ∧
        Tendsto s atTop (𝓝 1)) := by
  refine ⟨countable_nonzero_atoms nu, ?_, ?_, ?_,
    exists_null_seq_below_one nu, exists_null_seq_above_one nu⟩
  · intro U hU hUne
    exact exists_null_atom_mem_open nu hU hUne
  · intro s htail
    obtain ⟨r, hsr, hnull, htailr⟩ := exists_null_tail_threshold nu s htail
    exact ⟨r, lt_of_le_of_lt (le_max_left s 0) hsr,
      hnull, htailr⟩
  · intro a1 a2 ha1 ha12 hs1 hs2
    exact exists_null_between_support nu ha1 ha12 hs1 hs2

/-! ## Two upper thresholds -/

/-- Two ordered upper parameters have finite null points on both sides of
the lower one.  Finiteness of the chosen points follows from the displayed
strict upper bounds, including when `alpha2 = ⊤`. -/
theorem twoUpperNullThresholds (nu : Measure Param) [IsFiniteMeasure nu]
    {alpha1 alpha2 : Param} (h1 : (1 : Param) < alpha1)
    (h12 : alpha1 < alpha2) :
    ∃ a b : ℝ,
      1 < a ∧ finiteParam a < alpha1 ∧
      alpha1 < finiteParam b ∧ finiteParam b < alpha2 ∧
      nu ({finiteParam a} : Set Param) = 0 ∧
      nu ({finiteParam b} : Set Param) = 0 := by
  obtain ⟨pa, hpa, hnulla⟩ := exists_null_atom_mem_open nu isOpen_Ioo
    (nonempty_Ioo.mpr h1)
  obtain ⟨pb, hpb, hnullb⟩ := exists_null_atom_mem_open nu isOpen_Ioo
    (nonempty_Ioo.mpr h12)
  have hpaTop : pa ≠ (⊤ : Param) :=
    ne_top_of_lt (hpa.2.trans h12 |>.trans_le le_top)
  have hpbTop : pb ≠ (⊤ : Param) := by
    by_cases htop : alpha2 = (⊤ : Param)
    · subst alpha2
      exact ne_of_lt hpb.2
    · exact ne_top_of_lt (hpb.2.trans_le le_top)
  let a := ENNReal.toReal pa
  let b := ENNReal.toReal pb
  have haFinite : finiteParam a = pa := finiteParam_paramToReal pa hpaTop
  have hbFinite : finiteParam b = pb := finiteParam_paramToReal pb hpbTop
  have hOneA : 1 < a := by
    have hone : (1 : Param) < finiteParam a := by
      rw [haFinite]
      exact hpa.1
    change ((1 : NNReal) : WithTop NNReal) <
      ((a.toNNReal : NNReal) : WithTop NNReal) at hone
    rw [WithTop.coe_lt_coe] at hone
    exact Real.one_lt_toNNReal.mp hone
  refine ⟨a, b, hOneA, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [haFinite] using hpa.2
  · simpa only [hbFinite] using hpb.1
  · simpa only [hbFinite] using hpb.2
  · simpa only [haFinite] using hnulla
  · simpa only [hbFinite] using hnullb

/-! ## Strict integral mass from support -/

/-- A support point and a nested open neighbourhood give strict positive
mass and strict lower/upper set-integral bounds. -/
theorem supportStrictIntegral (nu : Measure Param) [IsFiniteMeasure nu]
    (x : Param) (U V : Set Param) (f : Param → ℝ) (c : ℝ)
    (hxsupp : x ∈ suppMeasure nu)
    (hU : IsOpen U) (hxU : x ∈ U)
    (hV : IsOpen V) (hxV : x ∈ V) (hVU : V ⊆ U)
    (_hfmeas : Measurable f) (hfint : IntegrableOn f U nu) (hc : 0 < c) :
    0 < nu U ∧ 0 < nu V ∧
      ((∀ a ∈ U, 0 ≤ f a) →
        (∀ a ∈ V, c ≤ f a) →
        0 < c * ENNReal.toReal (nu V) ∧
          c * ENNReal.toReal (nu V) ≤ ∫ a in U, f a ∂nu) ∧
      ((∀ a ∈ U, f a ≤ 0) →
        (∀ a ∈ V, f a ≤ -c) →
        (∫ a in U, f a ∂nu) ≤ -c * ENNReal.toReal (nu V) ∧
          -c * ENNReal.toReal (nu V) < 0) := by
  have hUpos : 0 < nu U := measure_pos_of_mem_support_open hxsupp hU hxU
  have hVpos : 0 < nu V := measure_pos_of_mem_support_open hxsupp hV hxV
  have hVtop : nu V ≠ (⊤ : ENNReal) := measure_ne_top nu V
  have hVreal : 0 < ENNReal.toReal (nu V) :=
    ENNReal.toReal_pos hVpos.ne' hVtop
  have hfintV : IntegrableOn f V nu := hfint.mono_set hVU
  refine ⟨hUpos, hVpos, ?_, ?_⟩
  · intro hfU hfV
    have hlower : c * ENNReal.toReal (nu V) ≤ ∫ a in V, f a ∂nu := by
      exact setIntegral_ge_of_const_le_real hV.measurableSet hVtop hfV hfintV
    have hnonneg : 0 ≤ᵐ[nu.restrict U] f := by
      filter_upwards [self_mem_ae_restrict hU.measurableSet] with a ha
      exact hfU a ha
    have hmono : (∫ a in V, f a ∂nu) ≤ ∫ a in U, f a ∂nu := by
      apply setIntegral_mono_set hfint hnonneg
      exact Filter.Eventually.of_forall hVU
    exact ⟨mul_pos hc hVreal, hlower.trans hmono⟩
  · intro hfU hfV
    have hnegInt : IntegrableOn (fun a => -f a) U nu := hfint.neg
    have hnegIntV : IntegrableOn (fun a => -f a) V nu := hnegInt.mono_set hVU
    have hnegV : ∀ a ∈ V, c ≤ -f a := by
      intro a ha
      linarith [hfV a ha]
    have hlower : c * ENNReal.toReal (nu V) ≤
        ∫ a in V, -f a ∂nu := by
      exact setIntegral_ge_of_const_le_real hV.measurableSet hVtop hnegV hnegIntV
    have hnonneg : 0 ≤ᵐ[nu.restrict U] fun a => -f a := by
      filter_upwards [self_mem_ae_restrict hU.measurableSet] with a ha
      exact neg_nonneg.mpr (hfU a ha)
    have hmono : (∫ a in V, -f a ∂nu) ≤ ∫ a in U, -f a ∂nu := by
      apply setIntegral_mono_set hnegInt hnonneg
      exact Filter.Eventually.of_forall hVU
    have hbound := hlower.trans hmono
    rw [integral_neg] at hbound
    exact ⟨by linarith, by nlinarith [mul_pos hc hVreal]⟩

/-! ## Nonzero scalar witnesses -/

/-- Total variation of a nonzero real scalar multiple of a positive signed
measure. -/
theorem signedTV_smul_signedLift (c : ℝ) (hc : c ≠ 0)
    (sigma : FiniteMeasure Param) :
    signedTV (c • signedLift sigma) =
      ENNReal.ofReal |c| • finiteMeasure sigma := by
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · have hnonneg : 0 ≤ -c := neg_nonneg.mpr hcneg.le
    have hmu : c • signedLift sigma =
        negativeSigned (finiteScale (-c) hnonneg sigma) := by
      rw [negativeSigned_finiteScale]
      simp only [neg_neg, positiveSigned]
    rw [hmu, signedTV_negativeSigned]
    simp [finiteScale, finiteMeasure, abs_of_neg hcneg]
  · have hmu : c • signedLift sigma =
        positiveSigned (finiteScale c hcpos.le sigma) :=
      (positiveSigned_finiteScale c hcpos.le sigma).symm
    rw [hmu, signedTV_positiveSigned]
    simp [finiteScale, finiteMeasure, abs_of_pos hcpos]

/-- A nonzero positive scalar does not change the support of a measure. -/
theorem support_smul_of_pos {nu : Measure Param} (k : ENNReal) (hk : 0 < k) :
    (k • nu).support = nu.support := by
  rw [Measure.support_eq_forall_isOpen, Measure.support_eq_forall_isOpen]
  ext x
  constructor
  · intro hx U hxU hU
    have hprod := hx U hxU hU
    simp only [Measure.smul_apply, smul_eq_mul] at hprod
    exact (ENNReal.mul_pos_iff.mp hprod).2
  · intro hx U hxU hU
    have hpos := hx U hxU hU
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_pos hk.ne' hpos.ne'

/-- Literal total-variation, support, and null-atom package for a nonzero
real scalar witness. -/
theorem scalarMeasureSupport (c : ℝ) (hc : c ≠ 0)
    (sigma : FiniteMeasure Param) :
    let mu := c • signedLift sigma
    signedTV mu = ENNReal.ofReal |c| • finiteMeasure sigma ∧
      suppSigned mu = suppMeasure (finiteMeasure sigma) ∧
      ∀ r : Param,
        signedTV mu ({r} : Set Param) = 0 ↔
          finiteMeasure sigma ({r} : Set Param) = 0 := by
  dsimp only
  have htv := signedTV_smul_signedLift c hc sigma
  have hk : 0 < ENNReal.ofReal |c| :=
    ENNReal.ofReal_pos.mpr (abs_pos.mpr hc)
  refine ⟨htv, ?_, ?_⟩
  · rw [suppSigned, suppMeasure, htv]
    exact support_smul_of_pos _ hk
  · intro r
    rw [htv]
    simp [Measure.smul_apply, smul_eq_mul, hk.ne']

end ConditionalEntropy
