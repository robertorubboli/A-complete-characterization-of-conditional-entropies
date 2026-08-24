import ConditionalEntropy.PowerMean
import ConditionalEntropy.RenyiProperties
import ConditionalEntropy.FiniteExtrema

/-!
# Renyi entropy and compactified power means

This file proves the exact logarithmic power-mean identity used in the
finite-support factorisation.  It includes the compactified top endpoint and
uses only the total endpoint-aware Renyi definitions.
-/

noncomputable section

open Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

section

variable {I : Type u} [Fintype I] [Nonempty I]

omit [Fintype I] [Nonempty I] in
theorem exists_pos_coordinate_of_cone_ne (x : ConeVec I) (hx : x ≠ 0) :
    ∃ i, 0 < x.1 i := by
  by_contra h
  push Not at h
  apply hx
  apply Subtype.ext
  funext i
  exact le_antisymm (h i) (x.2 i)

omit [Nonempty I] in
theorem rawPowerSum_pos {r : ℝ}
    (x : ConeVec I) (hx : x ≠ 0) :
    0 < ∑ i, x.1 i ^ r := by
  obtain ⟨i, hi⟩ := exists_pos_coordinate_of_cone_ne x hx
  exact Finset.sum_pos' (fun j _ => Real.rpow_nonneg (x.2 j) r)
    ⟨i, Finset.mem_univ i, Real.rpow_pos_of_pos hi r⟩

theorem powerSum_normalize_toPosCone {r : ℝ} (x : ConeVec I) (hx : x ≠ 0) :
    powerSum r (normalize (toPosCone x hx)) =
      (∑ i, x.1 i ^ r) / (l1Mass x.1) ^ r := by
  have hm : 0 < l1Mass x.1 := (coneNonzeroMass x).mp hx
  unfold powerSum
  rw [Finset.sum_div]
  congr 1
  funext i
  change (x.1 i / l1Mass x.1) ^ r = x.1 i ^ r / l1Mass x.1 ^ r
  rw [Real.div_rpow (x.2 i) hm.le]

theorem finMax_normalize_toPosCone (x : ConeVec I) (hx : x ≠ 0) :
    finMax (normalize (toPosCone x hx)).1 =
      finMax x.1 / l1Mass x.1 := by
  have hm : 0 < l1Mass x.1 := (coneNonzeroMass x).mp hx
  apply le_antisymm
  · unfold finMax
    apply Finset.sup'_le Finset.univ_nonempty
    intro i _hi
    rw [normalize_apply]
    exact div_le_div_of_nonneg_right (le_finMax_apply x.1 i) hm.le
  · obtain ⟨i, hi⟩ := finMax_mem x.1
    have hpi : (normalize (toPosCone x hx)).1 i =
        finMax x.1 / l1Mass x.1 := by
      change x.1 i / l1Mass x.1 = finMax x.1 / l1Mass x.1
      rw [hi]
    rw [← hpi]
    exact le_finMax_apply (normalize (toPosCone x hx)).1 i

omit [Nonempty I] in
theorem lpNorm_log_identity {r : ℝ}
    (x : ConeVec I) (hx : x ≠ 0) :
    Real.log (lpNorm r x) =
      (1 / r) * Real.log (∑ i, x.1 i ^ r) := by
  have hsum : 0 < ∑ i, x.1 i ^ r := rawPowerSum_pos x hx
  unfold lpNorm
  rw [Real.log_rpow hsum]

/-- Exact finite-order normalized-cone identity away from zero and Shannon
order. -/
theorem renyiNormFormula_finite {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1)
    (x : ConeVec I) (hx : x ≠ 0) :
    renyi (finiteParam r) (normalize (toPosCone x hx)) =
      singularWeight (finiteParam r) *
        (Real.log (parameterPowerMean (finiteParam r) x) -
          Real.log (l1Mass x.1)) := by
  have hm : 0 < l1Mass x.1 := (coneNonzeroMass x).mp hx
  have hsum : 0 < ∑ i, x.1 i ^ r := rawPowerSum_pos x hx
  have hmrpow : 0 < (l1Mass x.1) ^ r := Real.rpow_pos_of_pos hm r
  rw [renyi_finite hr.le hr.ne' hr1]
  rw [singularWeight_finite hr.le hr1]
  rw [parameterPowerMean_finite hr.le hr.ne']
  rw [renyiFinite, powerSum_normalize_toPosCone]
  rw [Real.log_div hsum.ne' hmrpow.ne', Real.log_rpow hm]
  rw [lpNorm_log_identity x hx]
  field_simp [hr.ne', sub_ne_zero.mpr (Ne.symm hr1)]

/-- Exact normalized-cone identity at the compactified top order. -/
theorem renyiNormFormula_top (x : ConeVec I) (hx : x ≠ 0) :
    renyi (⊤ : Param) (normalize (toPosCone x hx)) =
      singularWeight (⊤ : Param) *
        (Real.log (parameterPowerMean (⊤ : Param) x) -
          Real.log (l1Mass x.1)) := by
  have hm : 0 < l1Mass x.1 := (coneNonzeroMass x).mp hx
  have hmax : 0 < finMax x.1 := by
    obtain ⟨i, hi⟩ := exists_pos_coordinate_of_cone_ne x hx
    exact hi.trans_le (le_finMax_apply x.1 i)
  rw [renyi_at_top, renyiTop, singularWeight_top,
    parameterPowerMean_top, finMax_normalize_toPosCone x hx]
  rw [Real.log_div hmax.ne' hm.ne']
  ring

/-- The manuscript's endpoint-aware Renyi--power-mean formula for every
nonzero, non-Shannon order, including `+∞`. -/
theorem renyiNormFormula (a : Param) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (x : ConeVec I) (hx : x ≠ 0) :
    renyi a (normalize (toPosCone x hx)) =
      singularWeight a *
        (Real.log (parameterPowerMean a x) - Real.log (l1Mass x.1)) := by
  induction a using WithTop.recTopCoe with
  | top => exact renyiNormFormula_top x hx
  | coe q =>
      have hq0 : (q : ℝ) ≠ 0 := by
        intro h
        apply ha0
        exact_mod_cast h
      have hqpos : 0 < (q : ℝ) := lt_of_le_of_ne q.2 (Ne.symm hq0)
      have hq1 : (q : ℝ) ≠ 1 := by
        intro h
        apply ha1
        exact_mod_cast h
      have hfinite : finiteParam (q : ℝ) = (q : Param) := by
        simp [finiteParam]
      rw [← hfinite]
      exact renyiNormFormula_finite hqpos hq1 x hx

end

end ConditionalEntropy
