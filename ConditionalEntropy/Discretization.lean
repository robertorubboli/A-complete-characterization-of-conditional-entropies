import ConditionalEntropy.Moments
import ConditionalEntropy.IntegratedEntropy
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Total finite-range discretizations of the Renyi parameter

The three maps in this file are total on the compactified parameter space.
Their branch order agrees with the manuscript: the lower grid is tested
first, then the Shannon point, and finally (for the exceptional map) the
distinguished upper point.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ConditionalEntropy

/-- Proof-carrying parameters strictly above the Shannon order. -/
abbrev UpperParam := {a : Param // 1 < a}

/-- The positive grid denominator `k + 2`. -/
def gridDenom (k : ℕ) : ℕ := k + 2

theorem gridDenom_pos (k : ℕ) : 0 < gridDenom k := by
  simp [gridDenom]

/-- The lower floor grid.  Its proof argument records that the parameter is
finite and lies below one; proof irrelevance makes the returned point
independent of the chosen proof. -/
def grid (k : ℕ) (a : Param) (_ha : a < 1) : Param :=
  ENNReal.ofReal
    ((Nat.floor (((gridDenom k : ℕ) : ℝ) * ENNReal.toReal a) : ℝ) /
      ((gridDenom k : ℕ) : ℝ))

/-- The grid point immediately below the Shannon order. -/
def shannonApprox (k : ℕ) : Param :=
  ENNReal.ofReal (1 - 1 / ((gridDenom k : ℕ) : ℝ))

/-- Total positive-temperature discretization. -/
def TPos (k : ℕ) (a : Param) : Param :=
  if ha : a < 1 then grid k a ha
  else if a = 1 then shannonApprox k
  else 0

/-- Total lower-support discretization, fixing the Shannon point. -/
def TLow (k : ℕ) (a : Param) : Param :=
  if ha : a < 1 then grid k a ha
  else if a = 1 then 1
  else 0

/-- Total exceptional discretization, fixing one distinguished upper point. -/
def TExc (astar : UpperParam) (k : ℕ) (a : Param) : Param :=
  if ha : a < 1 then grid k a ha
  else if a = 1 then shannonApprox k
  else if a = astar.1 then astar.1
  else 0

@[simp] theorem TPos_of_lt_one {k : ℕ} {a : Param} (ha : a < 1) :
    TPos k a = grid k a ha := by
  simp [TPos, ha]

@[simp] theorem TLow_of_lt_one {k : ℕ} {a : Param} (ha : a < 1) :
    TLow k a = grid k a ha := by
  simp [TLow, ha]

@[simp] theorem TExc_of_lt_one (astar : UpperParam) {k : ℕ} {a : Param}
    (ha : a < 1) : TExc astar k a = grid k a ha := by
  simp [TExc, ha]

@[simp] theorem TPos_one (k : ℕ) :
    TPos k 1 = shannonApprox k := by
  simp [TPos]

@[simp] theorem TLow_one (k : ℕ) : TLow k 1 = 1 := by
  simp [TLow]

@[simp] theorem TExc_one (astar : UpperParam) (k : ℕ) :
    TExc astar k 1 = shannonApprox k := by
  simp [TExc]

@[simp] theorem TExc_astar (astar : UpperParam) (k : ℕ) :
    TExc astar k astar.1 = astar.1 := by
  have hnot : ¬ astar.1 < 1 := not_lt.mpr astar.2.le
  have hne : astar.1 ≠ 1 := ne_of_gt astar.2
  simp [TExc, hnot, hne]

private theorem measurable_grid_formula (k : ℕ) : Measurable (fun a : Param =>
    ENNReal.ofReal
      ((Nat.floor (((gridDenom k : ℕ) : ℝ) * ENNReal.toReal a) : ℝ) /
        ((gridDenom k : ℕ) : ℝ))) := by
  apply ENNReal.measurable_ofReal.comp
  have hfloor : Measurable (fun a : Param =>
      Nat.floor (((gridDenom k : ℕ) : ℝ) * ENNReal.toReal a)) :=
    (measurable_const.mul ENNReal.measurable_toReal).nat_floor
  have hcast : Measurable (fun a : Param =>
      (Nat.floor (((gridDenom k : ℕ) : ℝ) * ENNReal.toReal a) : ℝ)) :=
    (measurable_of_countable fun n : ℕ => (n : ℝ)).comp hfloor
  exact hcast.div measurable_const

/-- Named Borel proof for the positive discretization. -/
theorem measurable_TPos (k : ℕ) : Measurable (TPos k) := by
  rw [show TPos k = fun a : Param =>
      if ha : a < 1 then
        ENNReal.ofReal
          ((Nat.floor (((gridDenom k : ℕ) : ℝ) * ENNReal.toReal a) : ℝ) /
            ((gridDenom k : ℕ) : ℝ))
      else if a = 1 then shannonApprox k
      else 0 by rfl]
  exact Measurable.ite measurableSet_Iio (measurable_grid_formula k)
    (Measurable.ite (measurableSet_singleton (1 : Param)) measurable_const measurable_const)

/-- Named Borel proof for the lower-support discretization. -/
theorem measurable_TLow (k : ℕ) : Measurable (TLow k) := by
  rw [show TLow k = fun a : Param =>
      if ha : a < 1 then
        ENNReal.ofReal
          ((Nat.floor (((gridDenom k : ℕ) : ℝ) * ENNReal.toReal a) : ℝ) /
            ((gridDenom k : ℕ) : ℝ))
      else if a = 1 then 1
      else 0 by rfl]
  exact Measurable.ite measurableSet_Iio (measurable_grid_formula k)
    (Measurable.ite (measurableSet_singleton (1 : Param)) measurable_const measurable_const)

/-- Named Borel proof for the exceptional discretization. -/
theorem measurable_TExc (astar : UpperParam) (k : ℕ) : Measurable (TExc astar k) := by
  rw [show TExc astar k = fun a : Param =>
      if ha : a < 1 then
        ENNReal.ofReal
          ((Nat.floor (((gridDenom k : ℕ) : ℝ) * ENNReal.toReal a) : ℝ) /
            ((gridDenom k : ℕ) : ℝ))
      else if a = 1 then shannonApprox k
      else if a = astar.1 then astar.1
      else 0 by rfl]
  exact Measurable.ite measurableSet_Iio (measurable_grid_formula k)
    (Measurable.ite (measurableSet_singleton (1 : Param)) measurable_const
      (Measurable.ite (measurableSet_singleton astar.1) measurable_const measurable_const))

/-- Bundled positive discretization of a probability measure. -/
def discPos (τ : ProbabilityMeasure Param) (k : ℕ) : ProbabilityMeasure Param :=
  probMap τ (TPos k) (measurable_TPos k).aemeasurable

/-- Bundled lower-support discretization of a probability measure. -/
def discLow (τ : ProbabilityMeasure Param) (k : ℕ) : ProbabilityMeasure Param :=
  probMap τ (TLow k) (measurable_TLow k).aemeasurable

/-- Bundled exceptional discretization of a probability measure. -/
def discExc (τ : ProbabilityMeasure Param) (astar : UpperParam) (k : ℕ) :
    ProbabilityMeasure Param :=
  probMap τ (TExc astar k) (measurable_TExc astar k).aemeasurable

private def gridValues (k : ℕ) : Set Param :=
  Set.range fun n : Fin (gridDenom k) =>
    ENNReal.ofReal ((n : ℝ) / ((gridDenom k : ℕ) : ℝ))

private theorem gridValues_finite (k : ℕ) : (gridValues k).Finite := by
  exact Set.finite_range _

private theorem grid_mem_gridValues (k : ℕ) (a : Param) (ha : a < 1) :
    grid k a ha ∈ gridValues k := by
  have ha_top : a ≠ ⊤ := by
    intro h
    subst a
    exact (not_lt_of_ge le_top) ha
  have har : ENNReal.toReal a < 1 := by
    have := (ENNReal.toReal_lt_toReal ha_top ENNReal.one_ne_top).mpr ha
    simpa using this
  have hq : 0 < gridDenom k := gridDenom_pos k
  have hqR : 0 < ((gridDenom k : ℕ) : ℝ) := by exact_mod_cast hq
  have hprod : ((gridDenom k : ℕ) : ℝ) * ENNReal.toReal a <
      ((gridDenom k : ℕ) : ℝ) := by
    nlinarith
  have hfloor : Nat.floor
      (((gridDenom k : ℕ) : ℝ) * ENNReal.toReal a) < gridDenom k := by
    exact (Nat.floor_lt' hq.ne').mpr hprod
  let n : Fin (gridDenom k) :=
    ⟨Nat.floor (((gridDenom k : ℕ) : ℝ) * ENNReal.toReal a), hfloor⟩
  exact ⟨n, by simp [grid, n]⟩

/-- The positive discretization has finite range for every grid level. -/
theorem finite_range_TPos (k : ℕ) : (Set.range (TPos k)).Finite := by
  refine ((gridValues_finite k).union
    (show ({shannonApprox k, 0} : Set Param).Finite by
      exact (Set.finite_singleton 0).insert _)).subset ?_
  rintro b ⟨a, rfl⟩
  by_cases ha : a < 1
  · exact Or.inl (by simpa only [TPos_of_lt_one ha] using grid_mem_gridValues k a ha)
  · by_cases h1 : a = 1
    · rw [TPos, dif_neg ha, if_pos h1]
      exact Or.inr (Set.mem_insert (shannonApprox k) {0})
    · rw [TPos, dif_neg ha, if_neg h1]
      exact Or.inr (Set.mem_insert_of_mem (shannonApprox k) (Set.mem_singleton 0))

/-- The lower-support discretization has finite range for every grid level. -/
theorem finite_range_TLow (k : ℕ) : (Set.range (TLow k)).Finite := by
  refine ((gridValues_finite k).union
    (show ({(1 : Param), 0} : Set Param).Finite by
      exact (Set.finite_singleton 0).insert _)).subset ?_
  rintro b ⟨a, rfl⟩
  by_cases ha : a < 1
  · exact Or.inl (by simpa only [TLow_of_lt_one ha] using grid_mem_gridValues k a ha)
  · by_cases h1 : a = 1
    · rw [TLow, dif_neg ha, if_pos h1]
      exact Or.inr (Set.mem_insert (1 : Param) {0})
    · rw [TLow, dif_neg ha, if_neg h1]
      exact Or.inr (Set.mem_insert_of_mem (1 : Param) (Set.mem_singleton 0))

/-- The exceptional discretization has finite range for every grid level. -/
theorem finite_range_TExc (astar : UpperParam) (k : ℕ) :
    (Set.range (TExc astar k)).Finite := by
  refine ((gridValues_finite k).union
    (show ({shannonApprox k, astar.1, 0} :
      Set Param).Finite by
        exact ((Set.finite_singleton 0).insert astar.1).insert _)).subset ?_
  rintro b ⟨a, rfl⟩
  by_cases ha : a < 1
  · exact Or.inl (by simpa only [TExc_of_lt_one astar ha] using grid_mem_gridValues k a ha)
  · by_cases h1 : a = 1
    · rw [TExc, dif_neg ha, if_pos h1]
      exact Or.inr (Set.mem_insert (shannonApprox k) {astar.1, 0})
    · by_cases hs : a = astar.1
      · rw [TExc, dif_neg ha, if_neg h1, if_pos hs]
        exact Or.inr (Set.mem_insert_of_mem (shannonApprox k)
          (Set.mem_insert astar.1 {0}))
      · rw [TExc, dif_neg ha, if_neg h1, if_neg hs]
        exact Or.inr (Set.mem_insert_of_mem (shannonApprox k)
          (Set.mem_insert_of_mem astar.1 (Set.mem_singleton 0)))

private theorem support_map_subset_range_of_finite
    {ν : Measure Param} {T : Param → Param} (hT : Measurable T)
    (hfin : (Set.range T).Finite) :
    (Measure.map T ν).support ⊆ Set.range T := by
  apply Measure.support_subset_of_isClosed hfin.isClosed
  rw [mem_ae_iff, Measure.map_apply hT hfin.isClosed.measurableSet.compl]
  simp

@[simp] theorem probMeasure_discPos (τ : ProbabilityMeasure Param) (k : ℕ) :
    probMeasure (discPos τ k) = Measure.map (TPos k) (probMeasure τ) := by
  rfl

@[simp] theorem probMeasure_discLow (τ : ProbabilityMeasure Param) (k : ℕ) :
    probMeasure (discLow τ k) = Measure.map (TLow k) (probMeasure τ) := by
  rfl

@[simp] theorem probMeasure_discExc (τ : ProbabilityMeasure Param)
    (astar : UpperParam) (k : ℕ) :
    probMeasure (discExc τ astar k) =
      Measure.map (TExc astar k) (probMeasure τ) := by
  rfl

/-- Every bundled positive discretization has finite measure support. -/
theorem finite_support_discPos (τ : ProbabilityMeasure Param) (k : ℕ) :
    (suppMeasure (probMeasure (discPos τ k))).Finite := by
  rw [probMeasure_discPos]
  exact (finite_range_TPos k).subset
    (support_map_subset_range_of_finite (measurable_TPos k) (finite_range_TPos k))

/-- Every bundled lower discretization has finite measure support. -/
theorem finite_support_discLow (τ : ProbabilityMeasure Param) (k : ℕ) :
    (suppMeasure (probMeasure (discLow τ k))).Finite := by
  rw [probMeasure_discLow]
  exact (finite_range_TLow k).subset
    (support_map_subset_range_of_finite (measurable_TLow k) (finite_range_TLow k))

/-- Every bundled exceptional discretization has finite measure support. -/
theorem finite_support_discExc (τ : ProbabilityMeasure Param)
    (astar : UpperParam) (k : ℕ) :
    (suppMeasure (probMeasure (discExc τ astar k))).Finite := by
  rw [probMeasure_discExc]
  exact (finite_range_TExc astar k).subset
    (support_map_subset_range_of_finite
      (measurable_TExc astar k) (finite_range_TExc astar k))

/-! ## Pointwise order facts and convergence -/

theorem grid_nonneg (k : ℕ) (a : Param) (ha : a < 1) :
    0 ≤ grid k a ha := bot_le

theorem grid_le (k : ℕ) (a : Param) (ha : a < 1) : grid k a ha ≤ a := by
  have ha_top : a ≠ ⊤ := by
    intro h
    subst a
    exact (not_lt_of_ge le_top) ha
  have hqR : 0 < ((gridDenom k : ℕ) : ℝ) := by
    exact_mod_cast gridDenom_pos k
  have hfloor :
      (Nat.floor (((gridDenom k : ℕ) : ℝ) * ENNReal.toReal a) : ℝ) ≤
        ((gridDenom k : ℕ) : ℝ) * ENNReal.toReal a := by
    exact Nat.floor_le (mul_nonneg hqR.le ENNReal.toReal_nonneg)
  have hdiv :
      (Nat.floor (((gridDenom k : ℕ) : ℝ) * ENNReal.toReal a) : ℝ) /
          ((gridDenom k : ℕ) : ℝ) ≤ ENNReal.toReal a := by
    rw [div_le_iff₀ hqR]
    simpa only [mul_comm] using hfloor
  change ENNReal.ofReal
      ((Nat.floor (((gridDenom k : ℕ) : ℝ) * ENNReal.toReal a) : ℝ) /
        ((gridDenom k : ℕ) : ℝ)) ≤ a
  exact ((ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mpr hdiv).trans_eq
    (ENNReal.ofReal_toReal ha_top)

theorem grid_lt_one (k : ℕ) (a : Param) (ha : a < 1) : grid k a ha < 1 :=
  (grid_le k a ha).trans_lt ha

private theorem singularWeight_mono_below_one {a b : Param}
    (hab : a ≤ b) (hb : b < 1) : singularWeight a ≤ singularWeight b := by
  have hb_top : b ≠ ⊤ := by
    intro h
    subst b
    exact (not_lt_of_ge le_top) hb
  have ha_top : a ≠ ⊤ := ne_top_of_le_ne_top hb_top hab
  have har_le : ENNReal.toReal a ≤ ENNReal.toReal b :=
    (ENNReal.toReal_le_toReal ha_top hb_top).mpr hab
  have hbr_lt : ENNReal.toReal b < 1 := by
    have := (ENNReal.toReal_lt_toReal hb_top ENNReal.one_ne_top).mpr hb
    simpa using this
  have har_lt : ENNReal.toReal a < 1 := har_le.trans_lt hbr_lt
  rw [singularWeight, dif_neg ha_top, singularWeight, dif_neg hb_top]
  change (if ENNReal.toReal a = 1 then 0
      else ENNReal.toReal a / (1 - ENNReal.toReal a)) ≤
    if ENNReal.toReal b = 1 then 0
      else ENNReal.toReal b / (1 - ENNReal.toReal b)
  rw [if_neg (ne_of_lt har_lt), if_neg (ne_of_lt hbr_lt)]
  rw [div_le_div_iff₀ (sub_pos.mpr har_lt) (sub_pos.mpr hbr_lt)]
  nlinarith

/-- On the lower interval the positive discretization rounds down and does
not increase the singular coefficient. -/
theorem TPos_lower_facts (k : ℕ) (a : Param) (ha : a ∈ Set.Ico (0 : Param) 1) :
    0 ≤ TPos k a ∧ TPos k a ≤ a ∧
      singularWeight (TPos k a) ≤ singularWeight a := by
  rw [TPos_of_lt_one ha.2]
  exact ⟨grid_nonneg k a ha.2, grid_le k a ha.2,
    singularWeight_mono_below_one (grid_le k a ha.2) ha.2⟩

private theorem tendsto_gridDenom_real :
    Tendsto (fun k : ℕ => ((gridDenom k : ℕ) : ℝ)) atTop atTop := by
  change Tendsto (Nat.cast ∘ fun k : ℕ => k + 2) atTop atTop
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2)

theorem tendsto_grid (a : Param) (ha : a < 1) :
    Tendsto (fun k : ℕ => grid k a ha) atTop (𝓝 a) := by
  have ha_top : a ≠ ⊤ := by
    intro h
    subst a
    exact (not_lt_of_ge le_top) ha
  have hreal : Tendsto (fun x : ℝ =>
      (Nat.floor (ENNReal.toReal a * x) : ℝ) / x) atTop
      (𝓝 (ENNReal.toReal a)) :=
    tendsto_nat_floor_mul_div_atTop ENNReal.toReal_nonneg
  have hcomp := hreal.comp tendsto_gridDenom_real
  have hof := ENNReal.tendsto_ofReal hcomp
  rw [ENNReal.ofReal_toReal ha_top] at hof
  exact hof.congr' <| Filter.Eventually.of_forall fun k => by
    simp only [grid, Function.comp_apply]
    rw [mul_comm]

theorem tendsto_shannonApprox :
    Tendsto shannonApprox atTop (𝓝 (1 : Param)) := by
  have hinv : Tendsto (fun k : ℕ =>
      (((gridDenom k : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_gridDenom_real
  have hreal : Tendsto (fun k : ℕ =>
      1 - (((gridDenom k : ℕ) : ℝ))⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hinv
  have hof := ENNReal.tendsto_ofReal hreal
  simp only [ENNReal.ofReal_one] at hof
  unfold shannonApprox
  simp only [one_div]
  exact hof

theorem tendsto_TPos_of_le_one (a : Param) (ha : a ≤ 1) :
    Tendsto (fun k : ℕ => TPos k a) atTop (𝓝 a) := by
  rcases ha.lt_or_eq with hlt | rfl
  · exact (tendsto_grid a hlt).congr' <|
      Filter.Eventually.of_forall fun k => (TPos_of_lt_one hlt).symm
  · simpa only [TPos_one] using tendsto_shannonApprox

theorem tendsto_TLow_of_le_one (a : Param) (ha : a ≤ 1) :
    Tendsto (fun k : ℕ => TLow k a) atTop (𝓝 a) := by
  rcases ha.lt_or_eq with hlt | rfl
  · exact (tendsto_grid a hlt).congr' <|
      Filter.Eventually.of_forall fun k => (TLow_of_lt_one hlt).symm
  · simpa only [TLow_one] using tendsto_const_nhds

theorem tendsto_TExc_of_le_one_or_eq (astar : UpperParam) (a : Param)
    (ha : a ≤ 1 ∨ a = astar.1) :
    Tendsto (fun k : ℕ => TExc astar k a) atTop (𝓝 a) := by
  rcases ha with hle | rfl
  · rcases hle.lt_or_eq with hlt | rfl
    · exact (tendsto_grid a hlt).congr' <|
        Filter.Eventually.of_forall fun k => (TExc_of_lt_one astar hlt).symm
    · simpa only [TExc_one] using tendsto_shannonApprox
  · simpa only [TExc_astar] using tendsto_const_nhds

/-- The literal finite-range, finite-support, order, and convergence package
for the three total discretizations. -/
theorem discretization_basic_package (τ : ProbabilityMeasure Param)
    (astar : UpperParam) (k : ℕ) :
    ((Set.range (TPos k)).Finite ∧
      (Set.range (TLow k)).Finite ∧
      (Set.range (TExc astar k)).Finite) ∧
    ((suppMeasure (probMeasure (discPos τ k))).Finite ∧
      (suppMeasure (probMeasure (discLow τ k))).Finite ∧
      (suppMeasure (probMeasure (discExc τ astar k))).Finite) ∧
    (∀ a ∈ Set.Ico (0 : Param) 1,
      0 ≤ TPos k a ∧ TPos k a ≤ a ∧
        singularWeight (TPos k a) ≤ singularWeight a) ∧
    ((∀ a : Param, a ≤ 1 →
        Tendsto (fun m : ℕ => TPos m a) atTop (𝓝 a)) ∧
      (∀ a : Param, a ≤ 1 →
        Tendsto (fun m : ℕ => TLow m a) atTop (𝓝 a)) ∧
      (∀ a : Param, (a ≤ 1 ∨ a = astar.1) →
        Tendsto (fun m : ℕ => TExc astar m a) atTop (𝓝 a))) := by
  exact ⟨⟨finite_range_TPos k, finite_range_TLow k, finite_range_TExc astar k⟩,
    ⟨finite_support_discPos τ k, finite_support_discLow τ k,
      finite_support_discExc τ astar k⟩,
    fun a ha => TPos_lower_facts k a ha,
    ⟨fun a ha => tendsto_TPos_of_le_one a ha,
      fun a ha => tendsto_TLow_of_le_one a ha,
      fun a ha => tendsto_TExc_of_le_one_or_eq astar a ha⟩⟩

private theorem ae_mem_of_support_subset {ν : Measure Param} {s : Set Param}
    (h : suppMeasure ν ⊆ s) : ∀ᵐ a ∂ν, a ∈ s := by
  filter_upwards [Measure.support_mem_ae (μ := ν)] with a ha
  exact h ha

private theorem ae_ne_of_singleton_measure_zero {ν : Measure Param} {x : Param}
    (h : ν {x} = 0) : ∀ᵐ a ∂ν, a ≠ x := by
  rw [ae_iff]
  have hset : {a : Param | ¬a ≠ x} = {x} := by
    ext a
    simp
  rw [hset]
  exact h

private theorem support_map_subset_finite_set
    {ν : Measure Param} {T : Param → Param} {s : Set Param}
    (hT : Measurable T) (hs : s.Finite) (hae : ∀ᵐ a ∂ν, T a ∈ s) :
    (Measure.map T ν).support ⊆ s := by
  apply Measure.support_subset_of_isClosed hs.isClosed
  rw [mem_ae_iff, Measure.map_apply hT hs.isClosed.measurableSet.compl]
  have hnull := ae_iff.mp hae
  have hset : T ⁻¹' sᶜ = {a : Param | ¬T a ∈ s} := by
    ext a
    simp
  rw [hset]
  exact hnull

private theorem support_discPos_subset (τ : ProbabilityMeasure Param) (k : ℕ)
    (hsupp : suppMeasure (probMeasure τ) ⊆ Set.Icc (0 : Param) 1)
    (hatom : probMeasure τ {1} = 0) :
    suppMeasure (probMeasure (discPos τ k)) ⊆ Set.Ico (0 : Param) 1 := by
  rw [probMeasure_discPos]
  let s := Set.range (TPos k) ∩ Set.Ico (0 : Param) 1
  have hsfin : s.Finite := (finite_range_TPos k).inter_of_left _
  have haeSupp := ae_mem_of_support_subset hsupp
  have haeNe := ae_ne_of_singleton_measure_zero hatom
  have hae : ∀ᵐ a ∂probMeasure τ, TPos k a ∈ s := by
    filter_upwards [haeSupp, haeNe] with a ha hne
    have hlt : a < 1 := lt_of_le_of_ne ha.2 hne
    exact ⟨⟨a, rfl⟩, by
      rw [TPos_of_lt_one hlt]
      exact ⟨grid_nonneg k a hlt, grid_lt_one k a hlt⟩⟩
  exact (support_map_subset_finite_set (measurable_TPos k) hsfin hae).trans
    Set.inter_subset_right

private theorem support_discLow_subset (τ : ProbabilityMeasure Param) (k : ℕ)
    (hsupp : suppMeasure (probMeasure τ) ⊆ Set.Icc (0 : Param) 1) :
    suppMeasure (probMeasure (discLow τ k)) ⊆ Set.Icc (0 : Param) 1 := by
  rw [probMeasure_discLow]
  let s := Set.range (TLow k) ∩ Set.Icc (0 : Param) 1
  have hsfin : s.Finite := (finite_range_TLow k).inter_of_left _
  have haeSupp := ae_mem_of_support_subset hsupp
  have hae : ∀ᵐ a ∂probMeasure τ, TLow k a ∈ s := by
    filter_upwards [haeSupp] with a ha
    refine ⟨⟨a, rfl⟩, ?_⟩
    rcases ha.2.lt_or_eq with hlt | rfl
    · rw [TLow_of_lt_one hlt]
      exact ⟨grid_nonneg k a hlt, (grid_le k a hlt).trans ha.2⟩
    · rw [TLow_one]
      exact ha
  exact (support_map_subset_finite_set (measurable_TLow k) hsfin hae).trans
    Set.inter_subset_right

private theorem support_discExc_subset (τ : ProbabilityMeasure Param)
    (astar : UpperParam) (k : ℕ)
    (hsupp : suppMeasure (probMeasure τ) ⊆
      Set.Icc (0 : Param) 1 ∪ {astar.1})
    (hatom : probMeasure τ {1} = 0) :
    suppMeasure (probMeasure (discExc τ astar k)) ⊆
      Set.Ico (0 : Param) 1 ∪ {astar.1} := by
  rw [probMeasure_discExc]
  let s := Set.range (TExc astar k) ∩
    (Set.Ico (0 : Param) 1 ∪ {astar.1})
  have hsfin : s.Finite := (finite_range_TExc astar k).inter_of_left _
  have haeSupp := ae_mem_of_support_subset hsupp
  have haeNe := ae_ne_of_singleton_measure_zero hatom
  have hae : ∀ᵐ a ∂probMeasure τ, TExc astar k a ∈ s := by
    filter_upwards [haeSupp, haeNe] with a ha hne
    refine ⟨⟨a, rfl⟩, ?_⟩
    rcases ha with ha | ha
    · have hlt : a < 1 := lt_of_le_of_ne ha.2 hne
      left
      rw [TExc_of_lt_one astar hlt]
      exact ⟨grid_nonneg k a hlt, grid_lt_one k a hlt⟩
    · have heq : a = astar.1 := Set.mem_singleton_iff.mp ha
      subst a
      right
      simpa only [TExc_astar] using Set.mem_singleton astar.1
  exact (support_map_subset_finite_set (measurable_TExc astar k) hsfin hae).trans
    Set.inter_subset_right

private theorem singleton_one_measure_zero_of_support_Ico {ν : Measure Param}
    (hsupp : suppMeasure ν ⊆ Set.Ico (0 : Param) 1) : ν {1} = 0 := by
  apply measure_mono_null (t := (suppMeasure ν)ᶜ)
  · intro a ha
    have ha1 : a = 1 := Set.mem_singleton_iff.mp ha
    subst a
    intro hmem
    exact (lt_irrefl (1 : Param)) (hsupp hmem).2
  · exact Measure.measure_compl_support

private theorem singleton_one_measure_zero_of_support_exc {ν : Measure Param}
    (astar : UpperParam)
    (hsupp : suppMeasure ν ⊆ Set.Ico (0 : Param) 1 ∪ {astar.1}) :
    ν {1} = 0 := by
  apply measure_mono_null (t := (suppMeasure ν)ᶜ)
  · intro a ha
    have ha1 : a = 1 := Set.mem_singleton_iff.mp ha
    subst a
    intro hmem
    rcases hsupp hmem with hlow | hexc
    · exact (lt_irrefl (1 : Param)) hlow.2
    · have heq : (1 : Param) = astar.1 := Set.mem_singleton_iff.mp hexc
      exact (ne_of_lt astar.2) heq
  · exact Measure.measure_compl_support

/-! ## Pushforward moment control -/

theorem shannonApprox_nonneg (k : ℕ) : 0 ≤ shannonApprox k := bot_le

theorem shannonApprox_le_one (k : ℕ) : shannonApprox k ≤ (1 : Param) := by
  have hq : 0 < ((gridDenom k : ℕ) : ℝ) := by
    exact_mod_cast gridDenom_pos k
  have hreal : 1 - 1 / ((gridDenom k : ℕ) : ℝ) ≤ 1 := by
    exact sub_le_self _ (one_div_nonneg.mpr hq.le)
  unfold shannonApprox
  exact ENNReal.ofReal_le_one.mpr hreal

private theorem omegaLower_TPos_le_of_lt_one (k : ℕ) (a : Param) (ha : a < 1) :
    omegaLower (TPos k a) ≤ omegaLower a := by
  rw [TPos_of_lt_one ha]
  unfold omegaLower
  rw [if_pos ⟨grid_nonneg k a ha, grid_lt_one k a ha⟩,
    if_pos ⟨bot_le, ha⟩]
  exact ENNReal.ofReal_le_ofReal
    (singularWeight_mono_below_one (grid_le k a ha) ha)

private theorem omegaLower_TExc_le_of_lt_one (astar : UpperParam)
    (k : ℕ) (a : Param) (ha : a < 1) :
    omegaLower (TExc astar k a) ≤ omegaLower a := by
  rw [TExc_of_lt_one astar ha]
  unfold omegaLower
  rw [if_pos ⟨grid_nonneg k a ha, grid_lt_one k a ha⟩,
    if_pos ⟨bot_le, ha⟩]
  exact ENNReal.ofReal_le_ofReal
    (singularWeight_mono_below_one (grid_le k a ha) ha)

private theorem MUpper_eq_zero_of_support_Icc {ν : Measure Param}
    (hsupp : suppMeasure ν ⊆ Set.Icc (0 : Param) 1) : MUpper ν = 0 := by
  unfold MUpper
  rw [← lintegral_zero]
  apply lintegral_congr_ae
  have hae := ae_mem_of_support_subset hsupp
  filter_upwards [hae] with a ha
  unfold omegaUpper
  rw [if_neg (show a ∉ Set.Ioi (1 : Param) from not_lt_of_ge ha.2)]

private theorem MLower_discPos_le (τ : ProbabilityMeasure Param) (k : ℕ)
    (hsupp : suppMeasure (probMeasure τ) ⊆ Set.Icc (0 : Param) 1)
    (hatom : probMeasure τ {1} = 0) :
    MLower (probMeasure (discPos τ k)) ≤ MLower (probMeasure τ) := by
  rw [probMeasure_discPos]
  unfold MLower
  rw [lintegral_map measurable_omegaLower (measurable_TPos k)]
  apply lintegral_mono_ae
  have haeSupp := ae_mem_of_support_subset hsupp
  have haeNe := ae_ne_of_singleton_measure_zero hatom
  filter_upwards [haeSupp, haeNe] with a ha hne
  exact omegaLower_TPos_le_of_lt_one k a (lt_of_le_of_ne ha.2 hne)

private theorem MLower_discExc_le (τ : ProbabilityMeasure Param)
    (astar : UpperParam) (k : ℕ)
    (hsupp : suppMeasure (probMeasure τ) ⊆
      Set.Icc (0 : Param) 1 ∪ {astar.1})
    (hatom : probMeasure τ {1} = 0) :
    MLower (probMeasure (discExc τ astar k)) ≤ MLower (probMeasure τ) := by
  rw [probMeasure_discExc]
  unfold MLower
  rw [lintegral_map measurable_omegaLower (measurable_TExc astar k)]
  apply lintegral_mono_ae
  have haeSupp := ae_mem_of_support_subset hsupp
  have haeNe := ae_ne_of_singleton_measure_zero hatom
  filter_upwards [haeSupp, haeNe] with a ha hne
  rcases ha with ha | ha
  · exact omegaLower_TExc_le_of_lt_one astar k a (lt_of_le_of_ne ha.2 hne)
  · have heq : a = astar.1 := Set.mem_singleton_iff.mp ha
    subst a
    rw [TExc_astar]

private theorem MUpper_discExc_eq (τ : ProbabilityMeasure Param)
    (astar : UpperParam) (k : ℕ)
    (hsupp : suppMeasure (probMeasure τ) ⊆
      Set.Icc (0 : Param) 1 ∪ {astar.1}) :
    MUpper (probMeasure (discExc τ astar k)) = MUpper (probMeasure τ) := by
  rw [probMeasure_discExc]
  unfold MUpper
  rw [lintegral_map measurable_omegaUpper (measurable_TExc astar k)]
  apply lintegral_congr_ae
  have hae := ae_mem_of_support_subset hsupp
  filter_upwards [hae] with a ha
  rcases ha with ha | ha
  · have hmap : TExc astar k a ≤ 1 := by
      rcases ha.2.lt_or_eq with hlt | rfl
      · rw [TExc_of_lt_one astar hlt]
        exact (grid_le k a hlt).trans ha.2
      · rw [TExc_one]
        exact shannonApprox_le_one k
    unfold omegaUpper
    rw [if_neg (show TExc astar k a ∉ Set.Ioi (1 : Param) from not_lt_of_ge hmap),
      if_neg (show a ∉ Set.Ioi (1 : Param) from not_lt_of_ge ha.2)]
  · have heq : a = astar.1 := Set.mem_singleton_iff.mp ha
    subst a
    rw [TExc_astar]

/-- The exact support and moment return package for the bundled probability
discretizations. -/
theorem discretization_package (τ : ProbabilityMeasure Param)
    (astar : UpperParam) (k : ℕ) :
    ((suppMeasure (probMeasure τ) ⊆ Set.Icc (0 : Param) 1 ∧
        probMeasure τ {1} = 0) →
      suppMeasure (probMeasure (discPos τ k)) ⊆ Set.Ico (0 : Param) 1 ∧
      probMeasure (discPos τ k) {1} = 0 ∧
      MLower (probMeasure (discPos τ k)) ≤ MLower (probMeasure τ) ∧
      MUpper (probMeasure (discPos τ k)) = MUpper (probMeasure τ) ∧
      MUpper (probMeasure τ) = 0) ∧
    ((suppMeasure (probMeasure τ) ⊆ Set.Icc (0 : Param) 1) →
      suppMeasure (probMeasure (discLow τ k)) ⊆ Set.Icc (0 : Param) 1) ∧
    ((suppMeasure (probMeasure τ) ⊆
          Set.Icc (0 : Param) 1 ∪ {astar.1} ∧
        probMeasure τ {1} = 0) →
      suppMeasure (probMeasure (discExc τ astar k)) ⊆
          Set.Ico (0 : Param) 1 ∪ {astar.1} ∧
      probMeasure (discExc τ astar k) {1} = 0 ∧
      MLower (probMeasure (discExc τ astar k)) ≤ MLower (probMeasure τ) ∧
      MUpper (probMeasure (discExc τ astar k)) = MUpper (probMeasure τ) ∧
      (MomFin (probMeasure τ) →
        MomFin (probMeasure (discExc τ astar k)) ∧
        MReal (probMeasure (discExc τ astar k)) ≤ MReal (probMeasure τ))) := by
  constructor
  · rintro ⟨hsupp, hatom⟩
    have hsuppMap := support_discPos_subset τ k hsupp hatom
    have hUpper : MUpper (probMeasure τ) = 0 :=
      MUpper_eq_zero_of_support_Icc hsupp
    have hUpperMap : MUpper (probMeasure (discPos τ k)) = 0 :=
      MUpper_eq_zero_of_support_Icc (hsuppMap.trans Set.Ico_subset_Icc_self)
    exact ⟨hsuppMap, singleton_one_measure_zero_of_support_Ico hsuppMap,
      MLower_discPos_le τ k hsupp hatom, hUpperMap.trans hUpper.symm, hUpper⟩
  constructor
  · exact fun hsupp => support_discLow_subset τ k hsupp
  · rintro ⟨hsupp, hatom⟩
    have hsuppMap := support_discExc_subset τ astar k hsupp hatom
    have hLower := MLower_discExc_le τ astar k hsupp hatom
    have hUpper := MUpper_discExc_eq τ astar k hsupp
    refine ⟨hsuppMap,
      singleton_one_measure_zero_of_support_exc astar hsuppMap,
      hLower, hUpper, ?_⟩
    intro hMom
    have hMomMap : MomFin (probMeasure (discExc τ astar k)) := by
      exact ⟨hLower.trans_lt hMom.1, by rw [hUpper]; exact hMom.2⟩
    refine ⟨hMomMap, ?_⟩
    unfold MReal
    have htoReal :
        (MLower (probMeasure (discExc τ astar k))).toReal ≤
          (MLower (probMeasure τ)).toReal :=
      ENNReal.toReal_mono (ne_of_lt hMom.1) hLower
    rw [hUpper]
    linarith

/-! ## Shannon-order continuity needed by dominated convergence -/

private theorem hasDerivAt_rpow_order_one (p : ℝ) (hp : 0 ≤ p) :
    HasDerivAt (fun a : ℝ => p ^ a) (p * Real.log p) 1 := by
  rcases hp.eq_or_lt with rfl | hp
  · have hev : (fun a : ℝ => (0 : ℝ) ^ a) =ᶠ[𝓝 (1 : ℝ)] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with a ha
      simp [Real.zero_rpow (ne_of_gt ha)]
    have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 1 :=
      hasDerivAt_const (x := (1 : ℝ)) (c := (0 : ℝ))
    simpa using hconst.congr_of_eventuallyEq hev
  · have h := (hasDerivAt_id (x := (1 : ℝ))).const_rpow hp
    convert h using 1 <;> simp [mul_comm]

private theorem hasDerivAt_log_powerSum_one
    {I : Type*} [Fintype I] [Nonempty I] (p : ProbVec I) :
    HasDerivAt (fun a : ℝ => Real.log (powerSum a p))
      (∑ i, p.1 i * Real.log (p.1 i)) 1 := by
  have hsum : HasDerivAt (fun a : ℝ => ∑ i, p.1 i ^ a)
      (∑ i, p.1 i * Real.log (p.1 i)) 1 :=
    HasDerivAt.fun_sum fun i _ => hasDerivAt_rpow_order_one (p.1 i) (p.2.1 i)
  have hpowOne : powerSum 1 p = 1 := by
    simp only [powerSum, Real.rpow_one]
    simpa only [l1Mass] using p.2.2
  have hsum' : HasDerivAt (fun a : ℝ => powerSum a p)
      (∑ i, p.1 i * Real.log (p.1 i)) 1 := by
    simpa only [powerSum] using hsum
  have hlog := hsum'.log (by rw [hpowOne]; norm_num)
  simpa only [hpowOne, div_one] using hlog

/-- The ordinary finite-order formula converges from below to Shannon
entropy.  This is proved from the derivative of the finite power sum rather
than introduced as an additional premise. -/
theorem tendsto_renyiFinite_nhdsLT_one
    {I : Type*} [Fintype I] [Nonempty I] (p : ProbVec I) :
    Tendsto (fun a : ℝ => renyiFinite a p) (𝓝[<] (1 : ℝ))
      (𝓝 (renyiOne p)) := by
  let f : ℝ → ℝ := fun a => Real.log (powerSum a p)
  let D : ℝ := ∑ i, p.1 i * Real.log (p.1 i)
  have hderiv : HasDerivAt f D 1 := by
    exact hasDerivAt_log_powerSum_one p
  have hslope : Tendsto (slope f 1) (𝓝[<] (1 : ℝ)) (𝓝 D) :=
    hderiv.tendsto_slope.mono_left (nhdsLT_le_nhdsNE (1 : ℝ))
  have hneg := hslope.neg
  refine hneg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  have hne : a ≠ 1 := ne_of_lt ha
  have hpowOne : powerSum 1 p = 1 := by
    simp only [powerSum, Real.rpow_one]
    simpa only [l1Mass] using p.2.2
  rw [renyiFinite, slope_def_field]
  change -((f a - f 1) / (a - 1)) =
    Real.log (powerSum a p) / (1 - a)
  simp only [f, hpowOne, Real.log_one, sub_zero]
  field_simp
  ring

@[simp] theorem grid_zero (k : ℕ) (h0 : (0 : Param) < 1) :
    grid k 0 h0 = 0 := by
  exact le_antisymm (grid_le k 0 h0) bot_le

theorem shannonApprox_pos (k : ℕ) : 0 < shannonApprox k := by
  have hq : (1 : ℝ) < ((gridDenom k : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < gridDenom k by simp [gridDenom])
  have hinv : 1 / ((gridDenom k : ℕ) : ℝ) < 1 := by
    simpa only [one_div_one] using one_div_lt_one_div_of_lt (show (0 : ℝ) < 1 by norm_num) hq
  unfold shannonApprox
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hinv)

theorem shannonApprox_lt_one (k : ℕ) : shannonApprox k < (1 : Param) := by
  have hq : 0 < ((gridDenom k : ℕ) : ℝ) := by
    exact_mod_cast gridDenom_pos k
  unfold shannonApprox
  exact ENNReal.ofReal_lt_one.mpr (sub_lt_self _ (one_div_pos.mpr hq))

private theorem tendsto_renyi_grid_of_pos
    {I : Type*} [Fintype I] [Nonempty I] (p : ProbVec I)
    (a : Param) (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun k : ℕ => renyi (grid k a ha1) p) atTop (𝓝 (renyi a p)) := by
  have haTop : a ≠ ⊤ := by
    intro h
    subst a
    exact (not_lt_of_ge le_top) ha1
  have har0 : 0 < ENNReal.toReal a := ENNReal.toReal_pos ha0.ne' haTop
  have har1 : ENNReal.toReal a ≠ 1 := by
    have hlt := (ENNReal.toReal_lt_toReal haTop ENNReal.one_ne_top).mpr ha1
    simpa using ne_of_lt hlt
  have hreal : Tendsto (fun k : ℕ => ENNReal.toReal (grid k a ha1)) atTop
      (𝓝 (ENNReal.toReal a)) :=
    (ENNReal.tendsto_toReal haTop).comp (tendsto_grid a ha1)
  have hfinite := (continuousAt_renyiFinite p har0 har1).tendsto.comp hreal
  have hpos : ∀ᶠ k : ℕ in atTop, 0 < grid k a ha1 :=
    (tendsto_grid a ha1).eventually (Ioi_mem_nhds ha0)
  have hlim : renyi a p = renyiFinite (ENNReal.toReal a) p := by
    simp [renyi, haTop, ha0.ne', ne_of_lt ha1, paramToReal]
  rw [hlim]
  refine hfinite.congr' ?_
  filter_upwards [hpos] with k hk
  have htop : grid k a ha1 ≠ ⊤ := by
    intro h
    have hlt := grid_lt_one k a ha1
    rw [h] at hlt
    exact (not_lt_of_ge le_top) hlt
  have hzero : grid k a ha1 ≠ 0 := hk.ne'
  have hone : grid k a ha1 ≠ 1 := ne_of_lt (grid_lt_one k a ha1)
  simp [renyi, htop, hzero, hone, paramToReal, Function.comp_apply]

private theorem tendsto_renyi_grid
    {I : Type*} [Fintype I] [Nonempty I] (p : ProbVec I)
    (a : Param) (ha : a < 1) :
    Tendsto (fun k : ℕ => renyi (grid k a ha) p) atTop (𝓝 (renyi a p)) := by
  rcases eq_or_lt_of_le (bot_le : (0 : Param) ≤ a) with rfl | hpos
  · have hconst : Tendsto (fun _ : ℕ => renyi (⊥ : Param) p) atTop
        (𝓝 (renyi (⊥ : Param) p)) := tendsto_const_nhds
    exact hconst.congr' <| Filter.Eventually.of_forall fun k => by
      have hg : grid k (⊥ : Param) ha = ⊥ :=
        le_antisymm (grid_le k (⊥ : Param) ha) bot_le
      change renyi (⊥ : Param) p = renyi (grid k (⊥ : Param) ha) p
      rw [hg]
  · exact tendsto_renyi_grid_of_pos p a hpos ha

private theorem tendsto_renyi_shannonApprox
    {I : Type*} [Fintype I] [Nonempty I] (p : ProbVec I) :
    Tendsto (fun k : ℕ => renyi (shannonApprox k) p) atTop
      (𝓝 (renyiOne p)) := by
  have hreal : Tendsto (fun k : ℕ => ENNReal.toReal (shannonApprox k)) atTop
      (𝓝 (1 : ℝ)) := by
    have hcomp := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp tendsto_shannonApprox
    simp only [ENNReal.toReal_one] at hcomp
    exact hcomp.congr' <| Filter.Eventually.of_forall fun _ => rfl
  have hwithin : Tendsto (fun k : ℕ => ENNReal.toReal (shannonApprox k)) atTop
      (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hreal, Filter.Eventually.of_forall fun k => ?_⟩
    have htop : shannonApprox k ≠ ⊤ := by
      intro h
      have hlt := shannonApprox_lt_one k
      rw [h] at hlt
      exact (not_lt_of_ge le_top) hlt
    have hlt := (ENNReal.toReal_lt_toReal htop ENNReal.one_ne_top).mpr
      (shannonApprox_lt_one k)
    simpa using hlt
  have hfinite := (tendsto_renyiFinite_nhdsLT_one p).comp hwithin
  refine hfinite.congr' ?_
  filter_upwards with k
  have htop : shannonApprox k ≠ ⊤ := by
    intro h
    have hlt := shannonApprox_lt_one k
    rw [h] at hlt
    exact (not_lt_of_ge le_top) hlt
  have hzero : shannonApprox k ≠ 0 := (shannonApprox_pos k).ne'
  have hone : shannonApprox k ≠ 1 := ne_of_lt (shannonApprox_lt_one k)
  simp [renyi, htop, hzero, hone, paramToReal, Function.comp_apply]

private theorem tendsto_renyi_TPos_of_le_one
    {I : Type*} [Fintype I] [Nonempty I] (p : ProbVec I)
    (a : Param) (ha : a ≤ 1) :
    Tendsto (fun k : ℕ => renyi (TPos k a) p) atTop (𝓝 (renyi a p)) := by
  rcases ha.lt_or_eq with hlt | rfl
  · exact (tendsto_renyi_grid p a hlt).congr' <|
      Filter.Eventually.of_forall fun k => congrArg (fun b => renyi b p)
        (TPos_of_lt_one hlt).symm
  · simpa only [TPos_one, renyi_at_one] using tendsto_renyi_shannonApprox p

private theorem tendsto_renyi_TLow_of_le_one
    {I : Type*} [Fintype I] [Nonempty I] (p : ProbVec I)
    (a : Param) (ha : a ≤ 1) :
    Tendsto (fun k : ℕ => renyi (TLow k a) p) atTop (𝓝 (renyi a p)) := by
  rcases ha.lt_or_eq with hlt | rfl
  · exact (tendsto_renyi_grid p a hlt).congr' <|
      Filter.Eventually.of_forall fun k => congrArg (fun b => renyi b p)
        (TLow_of_lt_one hlt).symm
  · simpa only [TLow_one] using tendsto_const_nhds

private theorem tendsto_renyi_TExc_of_le_one_or_eq
    {I : Type*} [Fintype I] [Nonempty I] (p : ProbVec I)
    (astar : UpperParam) (a : Param) (ha : a ≤ 1 ∨ a = astar.1) :
    Tendsto (fun k : ℕ => renyi (TExc astar k a) p) atTop (𝓝 (renyi a p)) := by
  rcases ha with hle | rfl
  · rcases hle.lt_or_eq with hlt | rfl
    · exact (tendsto_renyi_grid p a hlt).congr' <|
        Filter.Eventually.of_forall fun k => congrArg (fun b => renyi b p)
          (TExc_of_lt_one astar hlt).symm
    · simpa only [TExc_one, renyi_at_one] using tendsto_renyi_shannonApprox p
  · simpa only [TExc_astar] using tendsto_const_nhds

/-! ## A common-measure dominated-convergence package -/

/-- Integrated Renyi entropy after the positive pushforward. -/
def discIntegralPos {I : Type*} [Fintype I] [Nonempty I]
    (ν : Measure Param) (p : ProbVec I) (k : ℕ) : ℝ :=
  integratedEntropyPos (Measure.map (TPos k) ν) p

/-- Integrated Renyi entropy after the lower-support pushforward. -/
def discIntegralLow {I : Type*} [Fintype I] [Nonempty I]
    (ν : Measure Param) (p : ProbVec I) (k : ℕ) : ℝ :=
  integratedEntropyPos (Measure.map (TLow k) ν) p

/-- Integrated Renyi entropy after the exceptional pushforward. -/
def discIntegralExc {I : Type*} [Fintype I] [Nonempty I]
    (ν : Measure Param) (p : ProbVec I) (astar : UpperParam) (k : ℕ) : ℝ :=
  integratedEntropyPos (Measure.map (TExc astar k) ν) p

private theorem tendsto_integratedEntropy_map_of_ae
    {I : Type*} [Fintype I] [Nonempty I] (p : ProbVec I)
    (ν : Measure Param) [IsFiniteMeasure ν]
    (T : ℕ → Param → Param) (hT : ∀ k, Measurable (T k))
    (hlim : ∀ᵐ a ∂ν,
      Tendsto (fun k : ℕ => renyi (T k a) p) atTop (𝓝 (renyi a p))) :
    Tendsto (fun k : ℕ => integratedEntropyPos (Measure.map (T k) ν) p)
      atTop (𝓝 (integratedEntropyPos ν p)) := by
  let C : ℝ := Real.log (Fintype.card I : ℝ)
  have hmeas : ∀ k, AEStronglyMeasurable (fun a => renyi (T k a) p) ν := by
    intro k
    exact ((measurable_renyi p).comp (hT k)).aestronglyMeasurable
  have hbound : ∀ k, ∀ᵐ a ∂ν, ‖renyi (T k a) p‖ ≤ C := by
    intro k
    exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (renyi_nonneg (T k a) p)]
      exact renyi_le_log_card (T k a) p
  have hCint : Integrable (fun _ : Param => C) ν := integrable_const C
  have hdct := tendsto_integral_of_dominated_convergence
    (fun _ : Param => C) hmeas hCint hbound hlim
  unfold integratedEntropyPos
  refine hdct.congr' <| Filter.Eventually.of_forall fun k => ?_
  exact (integral_map (hT k).aemeasurable
    (measurable_renyi p).aestronglyMeasurable).symm

/-- For one common finite measure, the three pushforward-integral sequences
converge to the original integrated Renyi entropy on precisely the manuscript
support branches. -/
theorem discretization_dct_package
    {I : Type*} [Fintype I] [Nonempty I] (p : ProbVec I)
    (ν : Measure Param) [IsFiniteMeasure ν] (astar : UpperParam) :
    ((suppMeasure ν ⊆ Set.Icc (0 : Param) 1 ∧ ν {1} = 0) →
      Tendsto (discIntegralPos ν p) atTop (𝓝 (integratedEntropyPos ν p))) ∧
    ((suppMeasure ν ⊆ Set.Icc (0 : Param) 1) →
      Tendsto (discIntegralLow ν p) atTop (𝓝 (integratedEntropyPos ν p))) ∧
    ((suppMeasure ν ⊆ Set.Icc (0 : Param) 1 ∪ {astar.1} ∧ ν {1} = 0) →
      Tendsto (discIntegralExc ν p astar) atTop
        (𝓝 (integratedEntropyPos ν p))) := by
  constructor
  · rintro ⟨hsupp, _hatom⟩
    have hae := ae_mem_of_support_subset hsupp
    have hlim : ∀ᵐ a ∂ν,
        Tendsto (fun k : ℕ => renyi (TPos k a) p) atTop (𝓝 (renyi a p)) := by
      filter_upwards [hae] with a ha
      exact tendsto_renyi_TPos_of_le_one p a ha.2
    exact tendsto_integratedEntropy_map_of_ae p ν (fun k => TPos k)
      measurable_TPos hlim
  constructor
  · intro hsupp
    have hae := ae_mem_of_support_subset hsupp
    have hlim : ∀ᵐ a ∂ν,
        Tendsto (fun k : ℕ => renyi (TLow k a) p) atTop (𝓝 (renyi a p)) := by
      filter_upwards [hae] with a ha
      exact tendsto_renyi_TLow_of_le_one p a ha.2
    exact tendsto_integratedEntropy_map_of_ae p ν (fun k => TLow k)
      measurable_TLow hlim
  · rintro ⟨hsupp, _hatom⟩
    have hae := ae_mem_of_support_subset hsupp
    have hlim : ∀ᵐ a ∂ν,
        Tendsto (fun k : ℕ => renyi (TExc astar k a) p) atTop (𝓝 (renyi a p)) := by
      filter_upwards [hae] with a ha
      exact tendsto_renyi_TExc_of_le_one_or_eq p astar a <| by
        rcases ha with ha | ha
        · exact Or.inl ha.2
        · exact Or.inr (Set.mem_singleton_iff.mp ha)
    exact tendsto_integratedEntropy_map_of_ae p ν (fun k => TExc astar k)
      (measurable_TExc astar) hlim

end ConditionalEntropy
