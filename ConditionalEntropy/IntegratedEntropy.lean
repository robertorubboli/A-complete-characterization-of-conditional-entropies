import ConditionalEntropy.FiniteChannels
import ConditionalEntropy.RenyiProperties
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Integrated Renyi entropy and conditional candidates

This module integrates the endpoint-aware finite Renyi family against raw
positive measures and finite signed measures.  It then defines the four total
conditional candidates by summing, minimizing, or maximizing over the bundled
subtype of positive-mass columns.  Zero columns are therefore never normalized.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u v

section Integrated

variable {I : Type u} [Fintype I] [Nonempty I]

/-! ### Measurability and the uniform entropy bound -/

/-- A fixed nonnegative or positive base raised to a real exponent is Borel
measurable.  At base zero it is the measurable function which is one at order
zero and zero elsewhere. -/
theorem measurable_const_rpow (c : ℝ) : Measurable (fun r : ℝ => c ^ r) := by
  by_cases hc : c = 0
  · subst c
    have heq : (fun r : ℝ => (0 : ℝ) ^ r) =
        fun r => if r = 0 then 1 else 0 := by
      funext r
      by_cases hr : r = 0
      · simp [hr]
      · simp [hr, Real.zero_rpow]
    rw [heq]
    exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const
  · exact (Real.continuous_const_rpow hc).measurable

/-- The endpoint-aware Renyi kernel is Borel measurable in its compactified
order parameter. -/
theorem measurable_renyi (p : ProbVec I) :
    Measurable (fun a : Param => renyi a p) := by
  let k : Param → ℝ := fun a => renyiFinite (ENNReal.toReal a) p
  have hk : Measurable k := by
    unfold k renyiFinite powerSum
    apply Measurable.div
    · apply Measurable.log
      exact Finset.measurable_sum _ fun i _ =>
        (measurable_const_rpow (p.1 i)).comp ENNReal.measurable_toReal
    · exact measurable_const.sub ENNReal.measurable_toReal
  have heq : (fun a : Param => renyi a p) =
      fun a => if a = ⊤ then renyiTop p
        else if a = 0 then renyiZero p
        else if a = 1 then renyiOne p
        else k a := by
    funext a
    unfold renyi
    split <;> rename_i htop
    · simp
    · split <;> rename_i hzero
      · simp
      · split <;> rename_i hone
        · simp
        · simp [k, paramToReal]
  rw [heq]
  apply Measurable.ite (measurableSet_singleton (⊤ : Param)) measurable_const
  apply Measurable.ite (measurableSet_singleton (0 : Param)) measurable_const
  exact Measurable.ite (measurableSet_singleton (1 : Param)) measurable_const hk

private theorem card_pos_real : 0 < (Fintype.card I : ℝ) := by
  exact_mod_cast Fintype.card_pos

/-- Jensen's power-sum estimate below the Shannon order, written in the form
whose logarithm gives the sharp entropy bound. -/
theorem powerSum_le_card_rpow {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (p : ProbVec I) :
    powerSum a p ≤ (Fintype.card I : ℝ) ^ (1 - a) := by
  let n : ℝ := Fintype.card I
  have hn : 0 < n := card_pos_real (I := I)
  have hw0 : ∀ i ∈ (Finset.univ : Finset I), 0 ≤ n⁻¹ := by
    intro _ _
    exact inv_nonneg.mpr hn.le
  have hw1 : ∑ _i ∈ (Finset.univ : Finset I), n⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change (Fintype.card I : ℝ) * n⁻¹ = 1
    exact mul_inv_cancel₀ hn.ne'
  have hmem : ∀ i ∈ (Finset.univ : Finset I), p.1 i ∈ Ici (0 : ℝ) := by
    intro i _
    exact p.2.1 i
  have hJ := (Real.concaveOn_rpow ha0 ha1).le_map_sum hw0 hw1 hmem
  have havg : ∑ i ∈ (Finset.univ : Finset I), n⁻¹ • p.1 i = n⁻¹ := by
    have hp : ∑ i, p.1 i = 1 := by simpa only [l1Mass] using p.2.2
    simp only [smul_eq_mul, ← Finset.mul_sum, hp, mul_one]
  rw [havg] at hJ
  simp only [smul_eq_mul, ← Finset.mul_sum] at hJ
  change n⁻¹ * powerSum a p ≤ n⁻¹ ^ a at hJ
  have hmul := mul_le_mul_of_nonneg_left hJ hn.le
  have hsimp : n * (n⁻¹ * powerSum a p) = powerSum a p := by field_simp
  rw [hsimp] at hmul
  calc
    powerSum a p ≤ n * n⁻¹ ^ a := hmul
    _ = n ^ (1 - a) := by
      rw [Real.inv_rpow hn.le, ← Real.rpow_neg hn.le]
      calc
        n * n ^ (-a) = n ^ 1 * n ^ (-a) := by rw [Real.rpow_one]
        _ = n ^ (1 + -a) := (Real.rpow_add hn 1 (-a)).symm
        _ = n ^ (1 - a) := by ring_nf
    _ = (Fintype.card I : ℝ) ^ (1 - a) := rfl

/-- Jensen's reverse power-sum estimate above the Shannon order. -/
theorem card_rpow_le_powerSum {a : ℝ} (ha : 1 ≤ a) (p : ProbVec I) :
    (Fintype.card I : ℝ) ^ (1 - a) ≤ powerSum a p := by
  let n : ℝ := Fintype.card I
  have hn : 0 < n := card_pos_real (I := I)
  have hw0 : ∀ i ∈ (Finset.univ : Finset I), 0 ≤ n⁻¹ := by
    intro _ _
    exact inv_nonneg.mpr hn.le
  have hw1 : ∑ _i ∈ (Finset.univ : Finset I), n⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change (Fintype.card I : ℝ) * n⁻¹ = 1
    exact mul_inv_cancel₀ hn.ne'
  have hmem : ∀ i ∈ (Finset.univ : Finset I), p.1 i ∈ Ici (0 : ℝ) := by
    intro i _
    exact p.2.1 i
  have hJ := (convexOn_rpow ha).map_sum_le hw0 hw1 hmem
  have havg : ∑ i ∈ (Finset.univ : Finset I), n⁻¹ • p.1 i = n⁻¹ := by
    have hp : ∑ i, p.1 i = 1 := by simpa only [l1Mass] using p.2.2
    simp only [smul_eq_mul, ← Finset.mul_sum, hp, mul_one]
  rw [havg] at hJ
  simp only [smul_eq_mul, ← Finset.mul_sum] at hJ
  change n⁻¹ ^ a ≤ n⁻¹ * powerSum a p at hJ
  have hmul := mul_le_mul_of_nonneg_left hJ hn.le
  have hsimp : n * (n⁻¹ * powerSum a p) = powerSum a p := by field_simp
  rw [hsimp] at hmul
  calc
    (Fintype.card I : ℝ) ^ (1 - a) = n * n⁻¹ ^ a := by
      change n ^ (1 - a) = n * n⁻¹ ^ a
      rw [Real.inv_rpow hn.le, ← Real.rpow_neg hn.le]
      calc
        n ^ (1 - a) = n ^ (1 + -a) := by ring_nf
        _ = n ^ 1 * n ^ (-a) := Real.rpow_add hn 1 (-a)
        _ = n * n ^ (-a) := by rw [Real.rpow_one]
    _ ≤ powerSum a p := hmul

/-- The ordinary nonendpoint formula is at most the entropy of the uniform
distribution. -/
theorem renyiFinite_le_log_card {a : ℝ} (ha0 : 0 < a) (ha1 : a ≠ 1)
    (p : ProbVec I) :
    renyiFinite a p ≤ Real.log (Fintype.card I : ℝ) := by
  have hn : 0 < (Fintype.card I : ℝ) := card_pos_real (I := I)
  have hpow : 0 < powerSum a p := powerSum_pos ha0 p
  rcases lt_or_gt_of_ne ha1 with ha_lt | ha_gt
  · have hden : 0 < 1 - a := sub_pos.mpr ha_lt
    rw [renyiFinite, div_le_iff₀ hden]
    calc
      Real.log (powerSum a p) ≤ Real.log ((Fintype.card I : ℝ) ^ (1 - a)) :=
        Real.strictMonoOn_log.monotoneOn hpow (Real.rpow_pos_of_pos hn _)
          (powerSum_le_card_rpow ha0.le ha_lt.le p)
      _ = (1 - a) * Real.log (Fintype.card I : ℝ) := Real.log_rpow hn (1 - a)
      _ = Real.log (Fintype.card I : ℝ) * (1 - a) := mul_comm _ _
  · have hden : 1 - a < 0 := sub_neg.mpr ha_gt
    rw [renyiFinite, div_le_iff_of_neg hden]
    calc
      Real.log (Fintype.card I : ℝ) * (1 - a) =
          Real.log ((Fintype.card I : ℝ) ^ (1 - a)) := by
        rw [Real.log_rpow hn]
        ring
      _ ≤ Real.log (powerSum a p) :=
        Real.strictMonoOn_log.monotoneOn (Real.rpow_pos_of_pos hn _) hpow
          (card_rpow_le_powerSum ha_gt.le p)

/-- Shannon entropy is at most the logarithm of the ambient cardinality. -/
theorem renyiOne_le_log_card (p : ProbVec I) :
    renyiOne p ≤ Real.log (Fintype.card I : ℝ) := by
  let n : ℝ := Fintype.card I
  have hn : 0 < n := card_pos_real (I := I)
  have hw0 : ∀ i ∈ (Finset.univ : Finset I), 0 ≤ n⁻¹ := by
    intro _ _
    exact inv_nonneg.mpr hn.le
  have hw1 : ∑ _i ∈ (Finset.univ : Finset I), n⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change (Fintype.card I : ℝ) * n⁻¹ = 1
    exact mul_inv_cancel₀ hn.ne'
  have hmem : ∀ i ∈ (Finset.univ : Finset I), p.1 i ∈ Ici (0 : ℝ) := by
    intro i _
    exact p.2.1 i
  have hJ := Real.convexOn_mul_log.map_sum_le hw0 hw1 hmem
  have havg : ∑ i ∈ (Finset.univ : Finset I), n⁻¹ • p.1 i = n⁻¹ := by
    have hp : ∑ i, p.1 i = 1 := by simpa only [l1Mass] using p.2.2
    simp only [smul_eq_mul, ← Finset.mul_sum, hp, mul_one]
  rw [havg] at hJ
  simp only [smul_eq_mul, ← Finset.mul_sum] at hJ
  have hmul := mul_le_mul_of_nonneg_left hJ hn.le
  have hsimp (z : ℝ) : n * (n⁻¹ * z) = z := by field_simp
  rw [hsimp, hsimp] at hmul
  unfold renyiOne
  have hneg := neg_le_neg hmul
  rw [Real.log_inv] at hneg
  simpa [n] using hneg

/-- Sharp uniform bound for the total endpoint-aware Renyi family. -/
theorem renyi_le_log_card (a : Param) (p : ProbVec I) :
    renyi a p ≤ Real.log (Fintype.card I : ℝ) := by
  unfold renyi
  split <;> rename_i htop
  · exact renyiTop_le_log_card p
  · split <;> rename_i hzero
    · exact renyiZero_le_log_card p
    · split <;> rename_i hone
      · exact renyiOne_le_log_card p
      · apply renyiFinite_le_log_card
        · exact ENNReal.toReal_pos hzero htop
        · intro hreal
          apply hone
          exact (ENNReal.toReal_eq_one_iff a).mp hreal

/-- The sharper uniform bound by the number of positive coordinates.  The
proof restricts the probability vector to its support and then uses the
zero-extension invariance of endpoint-aware Renyi entropy. -/
theorem renyi_le_log_support (a : Param) (p : ProbVec I) :
    renyi a p ≤ Real.log ((supportFinset p.1).card : ℝ) := by
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
  have he : zeroExtendProb e ps = p := by
    apply Subtype.ext
    funext i
    change zeroExtendRaw e ps.1 i = p.1 i
    by_cases hi : i ∈ supportFinset p.1
    · let j : S := ⟨i, hi⟩
      simpa [e, ps, j] using zeroExtendRaw_apply e ps.1 j
    · have hrange : i ∉ Set.range e := by
        rintro ⟨j, hj⟩
        subst i
        exact hi j.2
      rw [zeroExtendRaw, dif_neg hrange]
      have hzero : p.1 i = 0 := by
        simpa only [supportFinset, Finset.mem_filter, Finset.mem_univ,
          true_and, not_ne_iff] using hi
      exact hzero.symm
  calc
    renyi a p = renyi a (zeroExtendProb e ps) := congrArg (renyi a) he.symm
    _ = renyi a ps := renyi_zeroExtend a e ps
    _ ≤ Real.log ((supportFinset p.1).card : ℝ) := by
      simpa [S] using renyi_le_log_card a ps

/-- Positive-measure integral of endpoint-aware Renyi entropy.  The definition
is total for an arbitrary raw Borel measure; finiteness is imposed by the
analytic lemmas that use it. -/
def integratedEntropyPos (ν : Measure Param) (p : ProbVec I) : ℝ :=
  ∫ a, renyi a p ∂ν

/-- Integral of endpoint-aware Renyi entropy against a finite signed measure,
using its canonical Jordan decomposition. -/
def integratedEntropySigned (μ : SignedMeasure Param) (p : ProbVec I) : ℝ :=
  signedIntegral μ fun a => renyi a p

/-- The raw Dirac measure has singleton support. -/
theorem support_diracRaw (a : Param) :
    (diracRaw a).support = ({a} : Set Param) := by
  rw [Measure.support_eq_forall_isOpen]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    by_contra hxa
    have hopen : IsOpen ({a}ᶜ : Set Param) := isClosed_singleton.isOpen_compl
    have hxmem : x ∈ ({a}ᶜ : Set Param) := by simpa
    have hpos := hx ({a}ᶜ) hxmem hopen
    rw [diracRaw_apply a hopen.measurableSet] at hpos
    simp at hpos
  · intro hxa
    subst x
    intro s has hs
    rw [diracRaw_apply a hs.measurableSet]
    simp [has]

/-- Dirac integration evaluates the endpoint-aware entropy kernel. -/
@[simp] theorem integratedEntropyPos_dirac (a : Param) (p : ProbVec I) :
    integratedEntropyPos (diracRaw a) p = renyi a p := by
  change (∫ x, renyi x p ∂Measure.dirac a) = renyi a p
  exact integral_dirac _ _

/-- Literal Dirac integration-and-support package from the blueprint. -/
theorem integratedEntropy_dirac_package (a : Param) (p : ProbVec I) :
    integratedEntropyPos (diracRaw a) p = renyi a p ∧
      (diracRaw a).support = ({a} : Set Param) :=
  ⟨integratedEntropyPos_dirac a p, support_diracRaw a⟩

/-- Renyi entropy is integrable against every finite positive measure. -/
theorem integrable_renyi (ν : Measure Param) [IsFiniteMeasure ν]
    (p : ProbVec I) : Integrable (fun a => renyi a p) ν := by
  let C := Real.log (Fintype.card I : ℝ)
  have hC : 0 ≤ C := by
    exact Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := I))
  apply (integrable_const C).mono (measurable_renyi p).aestronglyMeasurable
  filter_upwards [] with a
  rw [Real.norm_eq_abs, abs_of_nonneg (renyi_nonneg a p), Real.norm_eq_abs,
    abs_of_nonneg hC]
  exact renyi_le_log_card a p

/-- Integrability of the Renyi kernel against both Jordan components. -/
theorem integrable_renyi_signed_parts (μ : SignedMeasure Param)
    (p : ProbVec I) :
    Integrable (fun a => renyi a p) (signedPos μ) ∧
      Integrable (fun a => renyi a p) (signedNeg μ) := by
  exact ⟨integrable_renyi _ p, integrable_renyi _ p⟩

/-- A finite-dimensional Renyi entropy is bounded by any declared ambient
cardinality bound. -/
theorem renyi_bounds (d : ℕ) (hd : Fintype.card I ≤ d)
    (a : Param) (p : ProbVec I) :
    0 ≤ renyi a p ∧ renyi a p ≤ Real.log (d : ℝ) := by
  have hcardpos : 0 < Fintype.card I := Fintype.card_pos
  have hdpos : 0 < d := lt_of_lt_of_le hcardpos hd
  have hcast : (Fintype.card I : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hcardreal : 0 < (Fintype.card I : ℝ) := by exact_mod_cast hcardpos
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hlog : Real.log (Fintype.card I : ℝ) ≤ Real.log (d : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hcardreal hdreal hcast
  exact ⟨renyi_nonneg a p, (renyi_le_log_card a p).trans hlog⟩

/-- Positive integrated entropy is nonnegative and bounded by total mass
times the logarithmic alphabet bound. -/
theorem integratedEntropyPos_bounds (ν : Measure Param) [IsFiniteMeasure ν]
    (p : ProbVec I) (d : ℕ) (hd : Fintype.card I ≤ d) :
    0 ≤ integratedEntropyPos ν p ∧
      integratedEntropyPos ν p ≤ ν.real Set.univ * Real.log (d : ℝ) := by
  have hf : Integrable (fun a => renyi a p) ν := integrable_renyi ν p
  have hCint : Integrable (fun _ : Param => Real.log (d : ℝ)) ν := integrable_const _
  constructor
  · exact integral_nonneg fun a => (renyi_bounds d hd a p).1
  · unfold integratedEntropyPos
    calc
      ∫ a, renyi a p ∂ν ≤ ∫ _a : Param, Real.log (d : ℝ) ∂ν :=
        integral_mono hf hCint fun a => (renyi_bounds d hd a p).2
      _ = ν.real Set.univ * Real.log (d : ℝ) := by
        rw [integral_const]
        rfl

/-- Probability-measure specialization of the positive upper bound. -/
theorem integratedEntropyPos_prob_le (τ : ProbabilityMeasure Param)
    (p : ProbVec I) (d : ℕ) (hd : Fintype.card I ≤ d) :
    integratedEntropyPos (probMeasure τ) p ≤ Real.log (d : ℝ) := by
  letI : IsFiniteMeasure (probMeasure τ) := by
    unfold probMeasure
    infer_instance
  have h := (integratedEntropyPos_bounds (probMeasure τ) p d hd).2
  simpa [probMeasure] using h

/-- The Jordan signed integral agrees with Mathlib's vector-measure integral
whenever both Jordan components are integrable. -/
theorem signedIntegral_eq_vectorSignedIntegral_of_integrable
    {E : Type*} [MeasurableSpace E] (μ : SignedMeasure E) (f : E → ℝ)
    (hfpos : Integrable f (signedPos μ))
    (hfneg : Integrable f (signedNeg μ)) :
    signedIntegral μ f = vectorSignedIntegral μ f := by
  calc
    signedIntegral μ f =
        ∫ x, f x ∂μ.toJordanDecomposition.posPart -
          ∫ x, f x ∂μ.toJordanDecomposition.negPart := rfl
    _ = ∫ᵛ x, f x ∂<•μ.toJordanDecomposition.toSignedMeasure := by
      rw [JordanDecomposition.toSignedMeasure,
        VectorMeasure.integral_sub_vectorMeasure]
      · simp
      · simpa [VectorMeasure.Integrable, signedPos] using hfpos
      · simpa [VectorMeasure.Integrable, signedNeg] using hfneg
    _ = vectorSignedIntegral μ f := by
      rw [SignedMeasure.toSignedMeasure_toJordanDecomposition]
      rfl

/-- Absolute bound for integrated entropy against a finite signed measure. -/
theorem integratedEntropySigned_abs_le (μ : SignedMeasure Param)
    (p : ProbVec I) (d : ℕ) (hd : Fintype.card I ≤ d) :
    |integratedEntropySigned μ p| ≤
      Real.log (d : ℝ) * (signedTV μ).real Set.univ := by
  let f : Param → ℝ := fun a => renyi a p
  let C : ℝ := Real.log (d : ℝ)
  have hpos := integratedEntropyPos_bounds (signedPos μ) p d hd
  have hneg := integratedEntropyPos_bounds (signedNeg μ) p d hd
  have hpos0 : 0 ≤ ∫ a, f a ∂signedPos μ := by
    simpa [f, integratedEntropyPos] using hpos.1
  have hneg0 : 0 ≤ ∫ a, f a ∂signedNeg μ := by
    simpa [f, integratedEntropyPos] using hneg.1
  have htriangle :
      |(∫ a, f a ∂signedPos μ) - ∫ a, f a ∂signedNeg μ| ≤
        (∫ a, f a ∂signedPos μ) + ∫ a, f a ∂signedNeg μ := by
    calc
      |(∫ a, f a ∂signedPos μ) - ∫ a, f a ∂signedNeg μ| ≤
          |∫ a, f a ∂signedPos μ| + |∫ a, f a ∂signedNeg μ| := abs_sub _ _
      _ = (∫ a, f a ∂signedPos μ) + ∫ a, f a ∂signedNeg μ := by
        rw [abs_of_nonneg hpos0, abs_of_nonneg hneg0]
  unfold integratedEntropySigned signedIntegral
  change |(∫ a, f a ∂signedPos μ) - ∫ a, f a ∂signedNeg μ| ≤ _
  calc
    |(∫ a, f a ∂signedPos μ) - ∫ a, f a ∂signedNeg μ| ≤
        (∫ a, f a ∂signedPos μ) + ∫ a, f a ∂signedNeg μ := htriangle
    _ ≤ (signedPos μ).real Set.univ * C +
        (signedNeg μ).real Set.univ * C := add_le_add hpos.2 hneg.2
    _ = C * (signedTV μ).real Set.univ := by
      rw [signedTV_eq_add]
      simp only [Measure.real, Measure.add_apply,
        ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      ring

@[simp] theorem integratedEntropySigned_smul
    (μ : SignedMeasure Param) (t : ℝ) (p : ProbVec I) :
    integratedEntropySigned (t • μ) p =
      t * integratedEntropySigned μ p := by
  have hμ := integrable_renyi_signed_parts μ p
  have htμ := integrable_renyi_signed_parts (t • μ) p
  unfold integratedEntropySigned
  rw [signedIntegral_eq_vectorSignedIntegral_of_integrable _ _ htμ.1 htμ.2,
    signedIntegral_eq_vectorSignedIntegral_of_integrable _ _ hμ.1 hμ.2]
  simp [vectorSignedIntegral]

@[simp] theorem integratedEntropySigned_signedLift
    (σ : FiniteMeasure Param) (p : ProbVec I) :
    integratedEntropySigned (signedLift σ) p =
      integratedEntropyPos (finiteMeasure σ) p := by
  simp [integratedEntropySigned, integratedEntropyPos, finiteMeasure]

/-- Literal finiteness, positivity, boundedness, and scalar-linearity package
for the two integrated entropy carriers. -/
theorem integratedEntropy_finite_package
    (p : ProbVec I) (d : ℕ) (hd : Fintype.card I ≤ d)
    (μ : SignedMeasure Param) (σ : FiniteMeasure Param)
    (τ : ProbabilityMeasure Param) :
    |integratedEntropySigned μ p| ≤
        Real.log (d : ℝ) * (signedTV μ).real Set.univ ∧
      0 ≤ integratedEntropyPos (finiteMeasure σ) p ∧
      integratedEntropyPos (finiteMeasure σ) p ≤
        (finiteMeasure σ).real Set.univ * Real.log (d : ℝ) ∧
      integratedEntropyPos (probMeasure τ) p ≤ Real.log (d : ℝ) ∧
      ∀ t : ℝ, integratedEntropySigned (t • signedLift σ) p =
        t * integratedEntropyPos (finiteMeasure σ) p := by
  letI : IsFiniteMeasure (finiteMeasure σ) := by
    unfold finiteMeasure
    infer_instance
  have hσ := integratedEntropyPos_bounds (finiteMeasure σ) p d hd
  refine ⟨integratedEntropySigned_abs_le μ p d hd, hσ.1, hσ.2,
    integratedEntropyPos_prob_le τ p d hd, ?_⟩
  intro t
  rw [integratedEntropySigned_smul, integratedEntropySigned_signedLift]

end Integrated

/-! ## Total conditional candidates -/

/-- The positive exponential sum whose logarithm defines the finite,
nonzero-temperature candidate. -/
def temperateSum {X Y : Type u} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (t : ℝ) (τ : ProbabilityMeasure Param)
    (P : JointProb X Y) : ℝ := by
  classical
  exact ∑ y : Active P, colMass P y.1 *
    Real.exp (t * integratedEntropyPos (probMeasure τ) (conditional P y))

/-- Finite nonzero-temperature conditional entropy. -/
def HTemp (t : ℝ) (_ht : t ≠ 0) (τ : ProbabilityMeasure Param) :
    PolyJointFunctional.{u} :=
  fun P => Real.log (temperateSum t τ P) / t

/-- The derivation (zero-temperature) conditional entropy for a finite
positive parameter measure. -/
def HZero (σ : FiniteMeasure Param) : PolyJointFunctional.{u} :=
  fun P => by
    classical
    exact ∑ y : Active P, colMass P y.1 *
      integratedEntropyPos (finiteMeasure σ) (conditional P y)

/-- Negative tropical candidate: the minimum integrated entropy among active
conditioning columns. -/
def HMinus (τ : ProbabilityMeasure Param) : PolyJointFunctional.{u} :=
  fun P => by
    classical
    exact finMin fun y : Active P =>
      integratedEntropyPos (probMeasure τ) (conditional P y)

/-- Positive tropical candidate: the maximum integrated entropy among active
conditioning columns. -/
def HPlus (τ : ProbabilityMeasure Param) : PolyJointFunctional.{u} :=
  fun P => by
    classical
    exact finMax fun y : Active P =>
      integratedEntropyPos (probMeasure τ) (conditional P y)

/-- Every term of the finite-temperature exponential sum is positive, so the
sum is positive because the active subtype is nonempty. -/
theorem temperateSum_pos {X Y : Type u} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (t : ℝ) (τ : ProbabilityMeasure Param)
    (P : JointProb X Y) : 0 < temperateSum t τ P := by
  classical
  unfold temperateSum
  apply Finset.sum_pos'
  · intro y _
    exact mul_nonneg (active_colMass_pos P y).le (Real.exp_pos _).le
  · let y : Active P := Classical.choice (activeNonempty P)
    exact ⟨y, Finset.mem_univ y,
      mul_pos (active_colMass_pos P y) (Real.exp_pos _)⟩

/-- The four active-column candidates are nonnegative; the defining
finite-temperature exponential sum is strictly positive. -/
theorem conditionalCandidates_nonneg
    {X Y : Type u} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (P : JointProb X Y)
    (τ : ProbabilityMeasure Param) (σ : FiniteMeasure Param)
    (t : ℝ) (ht : t ≠ 0) :
    0 < temperateSum t τ P ∧ 0 ≤ HTemp t ht τ P ∧
      0 ≤ HZero σ P ∧ 0 ≤ HMinus τ P ∧ 0 ≤ HPlus τ P := by
  classical
  letI : IsFiniteMeasure (probMeasure τ) := by
    unfold probMeasure
    infer_instance
  letI : IsFiniteMeasure (finiteMeasure σ) := by
    unfold finiteMeasure
    infer_instance
  have hmass : ∑ y : Active P, colMass P y.1 = 1 := by
    calc
      ∑ y : Active P, colMass P y.1 =
          ∑ y ∈ activeFinset P, colMass P y :=
        (Finset.sum_subtype (activeFinset P) (fun _ => Iff.rfl)
          (fun y => colMass P y)).symm
      _ = 1 := (positiveColumnsNonempty P).2
  have hA (y : Active P) :
      0 ≤ integratedEntropyPos (probMeasure τ) (conditional P y) :=
    (integratedEntropyPos_bounds (probMeasure τ) (conditional P y)
      (Fintype.card X) le_rfl).1
  have hAσ (y : Active P) :
      0 ≤ integratedEntropyPos (finiteMeasure σ) (conditional P y) :=
    (integratedEntropyPos_bounds (finiteMeasure σ) (conditional P y)
      (Fintype.card X) le_rfl).1
  refine ⟨temperateSum_pos t τ P, ?_, ?_, ?_, ?_⟩
  · change 0 ≤ Real.log (temperateSum t τ P) / t
    rcases lt_or_gt_of_ne ht with htneg | htpos
    · apply div_nonneg_of_nonpos
      · apply Real.log_nonpos (temperateSum_pos t τ P).le
        rw [← hmass]
        unfold temperateSum
        apply Finset.sum_le_sum
        intro y _
        simpa using mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr
            (mul_nonpos_of_nonpos_of_nonneg htneg.le (hA y)))
          (active_colMass_pos P y).le
      · exact htneg.le
    · apply div_nonneg
      · apply Real.log_nonneg
        rw [← hmass]
        unfold temperateSum
        apply Finset.sum_le_sum
        intro y _
        simpa using mul_le_mul_of_nonneg_left
          (Real.one_le_exp (mul_nonneg htpos.le (hA y)))
          (active_colMass_pos P y).le
      · exact htpos.le
  · change 0 ≤ ∑ y : Active P, colMass P y.1 *
      integratedEntropyPos (finiteMeasure σ) (conditional P y)
    exact Finset.sum_nonneg fun y _ =>
      mul_nonneg (active_colMass_pos P y).le (hAσ y)
  · change 0 ≤ finMin (fun y : Active P =>
      integratedEntropyPos (probMeasure τ) (conditional P y))
    unfold finMin
    apply Finset.le_inf' Finset.univ_nonempty
    intro y _
    exact hA y
  · change 0 ≤ finMax (fun y : Active P =>
      integratedEntropyPos (probMeasure τ) (conditional P y))
    unfold finMax
    obtain ⟨y⟩ := activeNonempty P
    exact (hA y).trans (Finset.le_sup'
      (fun z : Active P =>
        integratedEntropyPos (probMeasure τ) (conditional P z))
      (Finset.mem_univ y))

end ConditionalEntropy
