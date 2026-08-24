import ConditionalEntropy.IntegratedEntropyAlgebra
import ConditionalEntropy.TropicalShapeReduction

/-!
# Necessity in the positive tropical branch

This module implements the simplex-face argument used to show that a
positive-tropical conditional entropy can be monotone only when its parameter
measure is concentrated at order zero.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

section ProbabilityCone

variable {I : Type u} [Fintype I] [Nonempty I]

/-- The strictly positive support of a finite probability vector. -/
def probSupport (p : ProbVec I) : Set I :=
  {i | 0 < p.1 i}

/-- The finite type carried by the strictly positive support. -/
abbrev ProbSupport (p : ProbVec I) :=
  {i : I // i ∈ probSupport p}

/-- Regard a probability vector as a nonzero vector in the nonnegative cone. -/
def probAsPosCone (p : ProbVec I) : PosConeVec I :=
  ⟨⟨p.1, p.2.1⟩, by
    intro hp
    have hmass := p.2.2
    rw [hp] at hmass
    simp [l1Mass] at hmass⟩

/-- Normalization and strict mixing commute literally with the
probability-to-cone embedding. -/
theorem probAsPosConeIdentities (p q : ProbVec I) (lambda : ℝ)
    (hlambda : 0 < lambda ∧ lambda < 1) :
    normalize (probAsPosCone p) = p ∧
      probAsPosCone
          (mixProbVec lambda ⟨hlambda.1.le, hlambda.2.le⟩ p q) =
        posMix lambda hlambda (probAsPosCone p) (probAsPosCone q) := by
  constructor
  · apply Subtype.ext
    funext i
    simp [probAsPosCone, normalize_apply, p.2.2]
  · apply Subtype.ext
    apply Subtype.ext
    rfl

omit [Nonempty I] in
/-- Every finite probability vector has a positive coordinate. -/
theorem probSupportNonempty (p : ProbVec I) :
    Nonempty (ProbSupport p) := by
  by_contra h
  have hpzero : p.1 = 0 := by
    funext i
    have hnpos : ¬ 0 < p.1 i := by
      intro hi
      exact h ⟨⟨i, hi⟩⟩
    exact le_antisymm (le_of_not_gt hnpos) (p.2.1 i)
  have hmass := p.2.2
  rw [hpzero] at hmass
  simp [l1Mass] at hmass

omit [Nonempty I] in
/-- Two probability vectors in the relative interior of the same simplex
face have a short affine decomposition within that face. -/
theorem sameSupportDecomposition (p q : ProbVec I)
    (hsupport : probSupport p = probSupport q) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      ∀ lambda : ℝ, 0 < lambda → lambda < eps →
        ∃ (hlambda : 0 ≤ lambda ∧ lambda ≤ 1) (r : ProbVec I),
          probSupport r = probSupport p ∧
            p = mixProbVec lambda hlambda q r := by
  classical
  letI : Nonempty (ProbSupport p) := probSupportNonempty p
  let ratio : ProbSupport p → ℝ := fun i ↦ p.1 i.1 / q.1 i.1
  have hqpos (i : ProbSupport p) : 0 < q.1 i.1 := by
    have hi : i.1 ∈ probSupport q := by
      exact hsupport ▸ i.2
    exact hi
  have hratio (i : ProbSupport p) : 0 < ratio i :=
    div_pos i.2 (hqpos i)
  have hminpos : 0 < finMin ratio := by
    obtain ⟨i, hi⟩ := finMin_mem ratio
    rw [← hi]
    exact hratio i
  let eps : ℝ := min 1 (finMin ratio)
  have hepspos : 0 < eps := lt_min zero_lt_one hminpos
  have hepsone : eps ≤ 1 := min_le_left _ _
  refine ⟨eps, hepspos, hepsone, ?_⟩
  intro lambda hlambda0 hlambdaeps
  have hlambda1 : lambda < 1 := hlambdaeps.trans_le hepsone
  let hclosed : 0 ≤ lambda ∧ lambda ≤ 1 :=
    ⟨hlambda0.le, hlambda1.le⟩
  let raw : I → ℝ := fun i ↦ (p.1 i - lambda * q.1 i) / (1 - lambda)
  have hden : 0 < 1 - lambda := sub_pos.mpr hlambda1
  have hraw_nonneg (i : I) : 0 ≤ raw i := by
    by_cases hipos : 0 < p.1 i
    · let j : ProbSupport p := ⟨i, hipos⟩
      have hlmin : lambda < finMin ratio :=
        hlambdaeps.trans_le (min_le_right _ _)
      have hlratio : lambda < p.1 i / q.1 i :=
        lt_of_lt_of_le hlmin (finMin_le ratio j)
      have hq : 0 < q.1 i := hqpos j
      have hmul : lambda * q.1 i < p.1 i :=
        (lt_div_iff₀ hq).mp hlratio
      exact div_nonneg (sub_nonneg.mpr hmul.le) hden.le
    · have hpzero : p.1 i = 0 :=
        le_antisymm (le_of_not_gt hipos) (p.2.1 i)
      have hqnot : ¬ 0 < q.1 i := by
        intro hq
        have hiq : i ∈ probSupport q := hq
        rw [← hsupport] at hiq
        exact hipos hiq
      have hqzero : q.1 i = 0 :=
        le_antisymm (le_of_not_gt hqnot) (q.2.1 i)
      simp [raw, hpzero, hqzero]
  have hraw_mass : l1Mass raw = 1 := by
    have hp : ∑ i, p.1 i = 1 := by
      simpa only [l1Mass] using p.2.2
    have hq : ∑ i, q.1 i = 1 := by
      simpa only [l1Mass] using q.2.2
    change (∑ i, (p.1 i - lambda * q.1 i) / (1 - lambda)) = 1
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hp, hq]
    field_simp [hden.ne']
  let r : ProbVec I := ⟨raw, hraw_nonneg, hraw_mass⟩
  have hr_support : probSupport r = probSupport p := by
    ext i
    simp only [probSupport, Set.mem_setOf_eq]
    constructor
    · intro hrpos
      by_contra hipos
      have hpzero : p.1 i = 0 :=
        le_antisymm (le_of_not_gt hipos) (p.2.1 i)
      have hqnot : ¬ 0 < q.1 i := by
        intro hq
        have hiq : i ∈ probSupport q := hq
        rw [← hsupport] at hiq
        exact hipos hiq
      have hqzero : q.1 i = 0 :=
        le_antisymm (le_of_not_gt hqnot) (q.2.1 i)
      simp [r, raw, hpzero, hqzero] at hrpos
    · intro hipos
      let j : ProbSupport p := ⟨i, hipos⟩
      have hlmin : lambda < finMin ratio :=
        hlambdaeps.trans_le (min_le_right _ _)
      have hlratio : lambda < p.1 i / q.1 i :=
        lt_of_lt_of_le hlmin (finMin_le ratio j)
      have hq : 0 < q.1 i := hqpos j
      have hnum : 0 < p.1 i - lambda * q.1 i := by
        rw [sub_pos]
        exact (lt_div_iff₀ hq).mp hlratio
      exact div_pos hnum hden
  refine ⟨hclosed, r, hr_support, ?_⟩
  apply Subtype.ext
  funext i
  change p.1 i = lambda * q.1 i +
    (1 - lambda) * ((p.1 i - lambda * q.1 i) / (1 - lambda))
  field_simp [hden.ne']
  ring

end ProbabilityCone

/-- A probability measure on the nonnegative compactified parameter line is
the Dirac mass at zero exactly when its positive open ray has measure zero. -/
theorem probabilityEqDiracZero (tau : ProbabilityMeasure Param) :
    probMeasure tau (Ioi (0 : Param)) = 0 ↔ tau = diracProb 0 := by
  constructor
  · intro htail
    apply ProbabilityMeasure.toMeasure_injective
    change probMeasure tau = probMeasure (diracProb 0)
    apply Measure.ext
    intro s hs
    rw [show probMeasure (diracProb 0) = diracRaw 0 from rfl,
      diracRaw_apply 0 hs]
    by_cases hzero : 0 ∈ s
    · have hcompl : sᶜ ⊆ Ioi (0 : Param) := by
        intro a ha
        have hane : a ≠ 0 := by
          intro hazero
          subst a
          exact ha hzero
        exact (pos_iff_ne_zero.mpr hane)
      have hcomplzero : probMeasure tau sᶜ = 0 :=
        measure_mono_null hcompl htail
      rw [measure_of_measure_compl_eq_zero hcomplzero]
      simp [probMeasure, hzero]
    · have hsubset : s ⊆ Ioi (0 : Param) := by
        intro a ha
        have hane : a ≠ 0 := by
          intro hazero
          subst a
          exact hzero ha
        exact pos_iff_ne_zero.mpr hane
      rw [measure_mono_null hsubset htail]
      simp [hzero]
  · rintro rfl
    rw [show probMeasure (diracProb 0) = diracRaw 0 from rfl,
      diracRaw_apply 0 measurableSet_Ioi]
    simp

private def binaryThird : ProbVec (Fin 2) :=
  binaryProb (1 / 3 : ℝ) (by norm_num) (by norm_num)

private theorem powerSum_binaryThird_lt {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    powerSum a binaryThird < (2 : ℝ) ^ (1 - a) := by
  have hc : StrictConcaveOn ℝ (Ici (0 : ℝ)) (fun x : ℝ ↦ x ^ a) :=
    Real.strictConcaveOn_rpow ha0 ha1
  have hstrict := hc.2
    (show (1 / 3 : ℝ) ∈ Ici 0 by norm_num)
    (show (2 / 3 : ℝ) ∈ Ici 0 by norm_num)
    (show (1 / 3 : ℝ) ≠ 2 / 3 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hsum :
      (1 / 3 : ℝ) ^ a + (2 / 3 : ℝ) ^ a <
        2 * (1 / 2 : ℝ) ^ a := by
    norm_num at hstrict ⊢
    nlinarith
  calc
    powerSum a binaryThird =
        (1 / 3 : ℝ) ^ a + (2 / 3 : ℝ) ^ a := by
      norm_num [powerSum, binaryThird, binaryProb, Fin.sum_univ_two]
    _ < 2 * (1 / 2 : ℝ) ^ a := hsum
    _ = (2 : ℝ) ^ (1 - a) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      norm_num [div_eq_mul_inv]

private theorem powerSum_binaryThird_gt {a : ℝ} (ha1 : 1 < a) :
    (2 : ℝ) ^ (1 - a) < powerSum a binaryThird := by
  have hc : StrictConvexOn ℝ (Ici (0 : ℝ)) (fun x : ℝ ↦ x ^ a) :=
    strictConvexOn_rpow ha1
  have hstrict := hc.2
    (show (1 / 3 : ℝ) ∈ Ici 0 by norm_num)
    (show (2 / 3 : ℝ) ∈ Ici 0 by norm_num)
    (show (1 / 3 : ℝ) ≠ 2 / 3 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hsum :
      2 * (1 / 2 : ℝ) ^ a <
        (1 / 3 : ℝ) ^ a + (2 / 3 : ℝ) ^ a := by
    norm_num at hstrict ⊢
    nlinarith
  calc
    (2 : ℝ) ^ (1 - a) = 2 * (1 / 2 : ℝ) ^ a := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      norm_num [div_eq_mul_inv]
    _ < (1 / 3 : ℝ) ^ a + (2 / 3 : ℝ) ^ a := hsum
    _ = powerSum a binaryThird := by
      norm_num [powerSum, binaryThird, binaryProb, Fin.sum_univ_two]

private theorem renyiFinite_binaryThird_lt_log_two {a : ℝ}
    (ha0 : 0 < a) (ha1 : a ≠ 1) :
    renyiFinite a binaryThird < Real.log 2 := by
  have hpowerpos : 0 < powerSum a binaryThird :=
    powerSum_pos ha0 binaryThird
  rcases lt_or_gt_of_ne ha1 with halt | hagt
  · have hden : 0 < 1 - a := sub_pos.mpr halt
    rw [renyiFinite, div_lt_iff₀ hden]
    calc
      Real.log (powerSum a binaryThird) <
          Real.log ((2 : ℝ) ^ (1 - a)) :=
        Real.strictMonoOn_log hpowerpos
          (Real.rpow_pos_of_pos (by norm_num) _)
          (powerSum_binaryThird_lt ha0 halt)
      _ = (1 - a) * Real.log 2 :=
        Real.log_rpow (by norm_num) (1 - a)
      _ = Real.log 2 * (1 - a) := mul_comm _ _
  · have hden : 1 - a < 0 := sub_neg.mpr hagt
    rw [renyiFinite, div_lt_iff_of_neg hden]
    calc
      Real.log 2 * (1 - a) = (1 - a) * Real.log 2 := mul_comm _ _
      _ = Real.log ((2 : ℝ) ^ (1 - a)) :=
        (Real.log_rpow (by norm_num) (1 - a)).symm
      _ < Real.log (powerSum a binaryThird) :=
        Real.strictMonoOn_log
          (Real.rpow_pos_of_pos (by norm_num) _) hpowerpos
          (powerSum_binaryThird_gt hagt)

private theorem renyiOne_binaryThird_lt_log_two :
    renyiOne binaryThird < Real.log 2 := by
  have hc : StrictConcaveOn ℝ (Ici (0 : ℝ)) Real.negMulLog :=
    Real.strictConcaveOn_negMulLog
  have hstrict := hc.2
    (show (1 / 3 : ℝ) ∈ Ici 0 by norm_num)
    (show (2 / 3 : ℝ) ∈ Ici 0 by norm_num)
    (show (1 / 3 : ℝ) ≠ 2 / 3 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hsum :
      Real.negMulLog (1 / 3 : ℝ) + Real.negMulLog (2 / 3 : ℝ) <
        2 * Real.negMulLog (1 / 2 : ℝ) := by
    norm_num at hstrict ⊢
    nlinarith
  calc
    renyiOne binaryThird =
        Real.negMulLog (1 / 3 : ℝ) + Real.negMulLog (2 / 3 : ℝ) := by
      norm_num [renyiOne, binaryThird, binaryProb, Fin.sum_univ_two,
        Real.negMulLog]
      ring
    _ < 2 * Real.negMulLog (1 / 2 : ℝ) := hsum
    _ = Real.log 2 := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
      simp [Real.negMulLog, Real.log_inv]

private theorem finMax_binaryThird :
    finMax binaryThird.1 = (2 / 3 : ℝ) := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := finMax_mem binaryThird.1
    rw [← hi]
    fin_cases i <;> norm_num [binaryThird, binaryProb]
  · have hi := le_finMax_apply binaryThird.1 (1 : Fin 2)
    norm_num [binaryThird, binaryProb] at hi ⊢
    exact hi

private theorem renyiTop_binaryThird_lt_log_two :
    renyiTop binaryThird < Real.log 2 := by
  rw [renyiTop, finMax_binaryThird]
  calc
    -Real.log (2 / 3 : ℝ) = Real.log (3 / 2 : ℝ) := by
      rw [← Real.log_inv]
      congr 1
      norm_num
    _ < Real.log 2 :=
      Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

private theorem renyi_binaryThird_lt_log_two {a : Param} (ha : 0 < a) :
    renyi a binaryThird < Real.log 2 := by
  by_cases htop : a = ⊤
  · subst a
    simpa using renyiTop_binaryThird_lt_log_two
  have hzero : a ≠ 0 := ha.ne'
  by_cases hone : a = 1
  · subst a
    simpa using renyiOne_binaryThird_lt_log_two
  have hrpos : 0 < paramToReal a htop :=
    ENNReal.toReal_pos hzero htop
  have hrone : paramToReal a htop ≠ 1 := by
    intro hr
    apply hone
    exact (ENNReal.toReal_eq_one_iff a).mp hr
  simpa [renyi, htop, hzero, hone] using
    renyiFinite_binaryThird_lt_log_two hrpos hrone

private abbrev LiftBit.{v} := ULift.{v} (Fin 2)

private def binaryThirdLift.{v} : ProbVec LiftBit.{v} :=
  zeroExtendProb Equiv.ulift.symm.toEmbedding binaryThird

@[simp] private theorem binaryThirdLift_up.{v} (i : Fin 2) :
    (binaryThirdLift.{v}).1 (ULift.up i) = binaryThird.1 i := by
  exact zeroExtendRaw_apply Equiv.ulift.symm.toEmbedding binaryThird.1 i

private theorem renyi_binaryThirdLift_lt_log_two.{v}
    {a : Param} (ha : 0 < a) :
    renyi a binaryThirdLift.{v} < Real.log 2 := by
  rw [binaryThirdLift, renyi_zeroExtend]
  exact renyi_binaryThird_lt_log_two ha

private theorem aTrop_eq_of_same_probSupport
    {I : Type u} [Fintype I] [Nonempty I]
    (tau : ProbabilityMeasure Param)
    (hmax : MaxQCave (aTrop tau : PosConeVec I → ℝ))
    (p q : ProbVec I) (hsupport : probSupport p = probSupport q) :
    aTrop tau (probAsPosCone p) = aTrop tau (probAsPosCone q) := by
  have hforward (p q : ProbVec I)
      (hsupport : probSupport p = probSupport q) :
      aTrop tau (probAsPosCone q) ≤ aTrop tau (probAsPosCone p) := by
    obtain ⟨eps, heps0, heps1, hdecomp⟩ :=
      sameSupportDecomposition p q hsupport
    let lambda : ℝ := eps / 2
    have hlambda0 : 0 < lambda := by
      dsimp [lambda]
      linarith
    have hlambdaeps : lambda < eps := by
      dsimp [lambda]
      linarith
    obtain ⟨hclosed, r, _hrsupport, hmix⟩ :=
      hdecomp lambda hlambda0 hlambdaeps
    have hlambda1 : lambda < 1 := lt_of_lt_of_le hlambdaeps heps1
    let hstrict : 0 < lambda ∧ lambda < 1 := ⟨hlambda0, hlambda1⟩
    let hstrictClosed : 0 ≤ lambda ∧ lambda ≤ 1 :=
      ⟨hlambda0.le, hlambda1.le⟩
    have hmixProb :
        p = mixProbVec lambda hstrictClosed q r := by
      calc
        p = mixProbVec lambda hclosed q r := hmix
        _ = mixProbVec lambda hstrictClosed q r := by rfl
    have hmixCone :=
      (probAsPosConeIdentities q r lambda hstrict).2
    calc
      aTrop tau (probAsPosCone q) ≤
          max (aTrop tau (probAsPosCone q))
            (aTrop tau (probAsPosCone r)) := le_max_left _ _
      _ ≤ aTrop tau
          (posMix lambda hstrict (probAsPosCone q) (probAsPosCone r)) :=
        hmax (probAsPosCone q) (probAsPosCone r) lambda hstrict
      _ = aTrop tau (probAsPosCone
          (mixProbVec lambda hstrictClosed q r)) := by
        rw [hmixCone]
      _ = aTrop tau (probAsPosCone p) := by rw [← hmixProb]
  exact le_antisymm
    (hforward q p hsupport.symm) (hforward p q hsupport)

/-- Conditional-majorization monotonicity of the positive tropical candidate
forces its parameter probability measure to be concentrated at order zero. -/
theorem positiveTropicalNecessity (tau : ProbabilityMeasure Param) :
    CMMonotone (HPlus tau : PolyJointFunctional.{u}) →
      tau = diracProb 0 := by
  intro hmono
  have hmaxAll :
      ∀ {X : Type u} [Fintype X] [Nonempty X],
        MaxQCave (aTrop tau : PosConeVec X → ℝ) :=
    (globalTropicalShapeReduction tau).2.mp hmono
  have hmaxTwo :
      MaxQCave (aTrop tau : PosConeVec LiftBit.{u} → ℝ) :=
    hmaxAll
  let uniformTwo : ProbVec LiftBit.{u} := uniformProb
  have hsupport :
      probSupport binaryThirdLift.{u} = probSupport uniformTwo := by
    ext i
    have hthirdPos : 0 < (binaryThirdLift.{u}).1 i := by
      rcases i with ⟨i⟩
      fin_cases i <;> norm_num [binaryThird, binaryProb]
    have huniformPos : 0 < uniformTwo.1 i := by
      dsimp [uniformTwo, uniformProb]
      positivity
    exact iff_of_true hthirdPos huniformPos
  have hface :
      aTrop tau (probAsPosCone binaryThirdLift.{u}) =
        aTrop tau (probAsPosCone uniformTwo) :=
    aTrop_eq_of_same_probSupport tau hmaxTwo binaryThirdLift.{u} uniformTwo hsupport
  have hnormThird :
      normalize (probAsPosCone binaryThirdLift.{u}) = binaryThirdLift.{u} :=
    (probAsPosConeIdentities binaryThirdLift.{u} binaryThirdLift.{u} (1 / 2 : ℝ)
      (by norm_num)).1
  have hnormUniform : normalize (probAsPosCone uniformTwo) = uniformTwo :=
    (probAsPosConeIdentities uniformTwo uniformTwo (1 / 2 : ℝ)
      (by norm_num)).1
  change integratedEntropyPos (probMeasure tau)
      (normalize (probAsPosCone binaryThirdLift.{u})) =
    integratedEntropyPos (probMeasure tau)
      (normalize (probAsPosCone uniformTwo)) at hface
  rw [hnormThird, hnormUniform] at hface
  have huniform :
      integratedEntropyPos (probMeasure tau) uniformTwo = Real.log 2 := by
    simpa [uniformTwo] using
      (integratedEntropyPos_prob_uniformProb tau (K := LiftBit.{u}))
  have hthird :
      integratedEntropyPos (probMeasure tau) binaryThirdLift.{u} = Real.log 2 :=
    hface.trans huniform
  letI : IsFiniteMeasure (probMeasure tau) := by
    unfold probMeasure
    infer_instance
  let gap : Param → ℝ :=
    fun a ↦ Real.log 2 - renyi a binaryThirdLift.{u}
  have hgapNonneg (a : Param) : 0 ≤ gap a := by
    have hbound := renyi_le_log_card a binaryThirdLift.{u}
    norm_num at hbound
    exact sub_nonneg.mpr hbound
  have hgapInt : Integrable gap (probMeasure tau) := by
    exact (integrable_const (Real.log 2)).sub
      (integrable_renyi (probMeasure tau) binaryThirdLift.{u})
  have hgapIntegral : ∫ a, gap a ∂probMeasure tau = 0 := by
    dsimp [gap]
    rw [integral_sub (integrable_const (Real.log 2))
      (integrable_renyi (probMeasure tau) binaryThirdLift.{u})]
    rw [integral_const]
    change (probMeasure tau).real univ * Real.log 2 -
        integratedEntropyPos (probMeasure tau) binaryThirdLift.{u} = 0
    rw [hthird]
    simp [probMeasure]
  have hgapZeroAE : gap =ᵐ[probMeasure tau] 0 :=
    (integral_eq_zero_iff_of_nonneg hgapNonneg hgapInt).mp hgapIntegral
  have htail : probMeasure tau (Ioi (0 : Param)) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hgapZeroAE] with a ha
    intro hapos
    have hstrict :
        renyi a binaryThirdLift.{u} < Real.log 2 :=
      renyi_binaryThirdLift_lt_log_two hapos
    have hgapPos : 0 < gap a := by
      dsimp [gap]
      linarith
    have hgapZero : gap a = 0 := by simpa using ha
    linarith
  exact probabilityEqDiracZero tau |>.mp htail

end ConditionalEntropy
