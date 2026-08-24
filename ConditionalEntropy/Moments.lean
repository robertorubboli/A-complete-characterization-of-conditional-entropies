import ConditionalEntropy.ParamMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Singular one-sided moments and admissible parameter ranges

The singular coefficient is never integrated as an unguarded signed
extended-real expression.  Its lower and upper parts are separate
nonnegative `ENNReal` kernels; the real moment is used only together with
the explicit `MomFin` guard.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ConditionalEntropy

/-- Support of a positive measure, under the name used by the blueprint. -/
def suppMeasure (ν : Measure Param) : Set Param :=
  ν.support

/-- Nonnegative singular kernel below order one. -/
def omegaLower (a : Param) : ENNReal :=
  if a ∈ Set.Ico (0 : Param) 1 then ENNReal.ofReal (singularWeight a) else 0

/-- Nonnegative absolute singular kernel above order one. -/
def omegaUpper (a : Param) : ENNReal :=
  if a ∈ Set.Ioi (1 : Param) then ENNReal.ofReal (-singularWeight a) else 0

/-- Lower one-sided singular moment. -/
def MLower (ν : Measure Param) : ENNReal :=
  ∫⁻ a, omegaLower a ∂ν

/-- Upper one-sided singular moment. -/
def MUpper (ν : Measure Param) : ENNReal :=
  ∫⁻ a, omegaUpper a ∂ν

/-- Both one-sided moments are finite. -/
def MomFin (ν : Measure Param) : Prop :=
  MLower ν < ⊤ ∧ MUpper ν < ⊤

/-- Total real value of the guarded signed moment. -/
def MReal (ν : Measure Param) : ℝ :=
  (MLower ν).toReal - (MUpper ν).toReal

@[simp] theorem omegaLower_zero : omegaLower (0 : Param) = 0 := by
  simp [omegaLower]

@[simp] theorem omegaLower_one : omegaLower (1 : Param) = 0 := by
  simp [omegaLower]

@[simp] theorem omegaLower_top : omegaLower (⊤ : Param) = 0 := by
  simp [omegaLower]

@[simp] theorem omegaUpper_zero : omegaUpper (0 : Param) = 0 := by
  simp [omegaUpper]

@[simp] theorem omegaUpper_one : omegaUpper (1 : Param) = 0 := by
  simp [omegaUpper]

@[simp] theorem omegaUpper_top : omegaUpper (⊤ : Param) = 1 := by
  simp [omegaUpper]

theorem measurable_singularWeight : Measurable singularWeight := by
  have heq : singularWeight = fun a : Param =>
      if a = ⊤ then -1
      else if ENNReal.toReal a = 1 then 0
      else ENNReal.toReal a / (1 - ENNReal.toReal a) := by
    funext a
    rw [singularWeight]
    rfl
  rw [heq]
  have hr : Measurable (fun a : Param => ENNReal.toReal a) :=
    ENNReal.measurable_toReal
  have hratio : Measurable (fun a : Param =>
      ENNReal.toReal a / (1 - ENNReal.toReal a)) :=
    hr.div (measurable_const.sub hr)
  have hinner : Measurable (fun a : Param =>
      if ENNReal.toReal a = 1 then 0
      else ENNReal.toReal a / (1 - ENNReal.toReal a)) :=
    Measurable.ite (measurableSet_eq_fun hr measurable_const)
      measurable_const hratio
  exact Measurable.ite (measurableSet_singleton (⊤ : Param))
    measurable_const hinner

theorem measurable_omegaLower : Measurable omegaLower := by
  unfold omegaLower
  apply Measurable.ite
  · exact measurableSet_Ico
  · exact ENNReal.measurable_ofReal.comp measurable_singularWeight
  · exact measurable_const

theorem measurable_omegaUpper : Measurable omegaUpper := by
  unfold omegaUpper
  apply Measurable.ite
  · exact measurableSet_Ioi
  · exact ENNReal.measurable_ofReal.comp measurable_singularWeight.neg
  · exact measurable_const

theorem measurable_singular_kernels :
    Measurable singularWeight ∧ Measurable omegaLower ∧ Measurable omegaUpper :=
  ⟨measurable_singularWeight, measurable_omegaLower, measurable_omegaUpper⟩

@[simp] theorem MLower_zero : MLower (0 : Measure Param) = 0 := by
  simp [MLower]

@[simp] theorem MUpper_zero : MUpper (0 : Measure Param) = 0 := by
  simp [MUpper]

theorem MLower_smul (c : ENNReal) (ν : Measure Param) :
    MLower (c • ν) = c * MLower ν := by
  simp [MLower, lintegral_smul_measure]

theorem MUpper_smul (c : ENNReal) (ν : Measure Param) :
    MUpper (c • ν) = c * MUpper ν := by
  simp [MUpper, lintegral_smul_measure]

theorem MLower_add (ν ρ : Measure Param) :
    MLower (ν + ρ) = MLower ν + MLower ρ := by
  simp [MLower, lintegral_add_measure]

theorem MUpper_add (ν ρ : Measure Param) :
    MUpper (ν + ρ) = MUpper ν + MUpper ρ := by
  simp [MUpper, lintegral_add_measure]

theorem MomFin_smul_iff {c : ℝ} (hc : 0 < c) (ν : Measure Param) :
    MomFin (ENNReal.ofReal c • ν) ↔ MomFin ν := by
  have hc0 : ENNReal.ofReal c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc
  have hctop : ENNReal.ofReal c < ⊤ := ENNReal.ofReal_lt_top
  simp only [MomFin, MLower_smul, MUpper_smul]
  constructor
  · rintro ⟨hlower, hupper⟩
    exact ⟨ENNReal.lt_top_of_mul_ne_top_right hlower.ne hc0,
      ENNReal.lt_top_of_mul_ne_top_right hupper.ne hc0⟩
  · rintro ⟨hlower, hupper⟩
    exact ⟨ENNReal.mul_lt_top hctop hlower, ENNReal.mul_lt_top hctop hupper⟩

theorem MReal_smul {c : ℝ} (hc : 0 ≤ c) (ν : Measure Param) :
    MReal (ENNReal.ofReal c • ν) = c * MReal ν := by
  simp only [MReal, MLower_smul, MUpper_smul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc]
  ring

@[simp] theorem MLower_dirac (a : Param) : MLower (diracRaw a) = omegaLower a := by
  change (∫⁻ x, omegaLower x ∂Measure.dirac a) = omegaLower a
  rw [lintegral_dirac' a measurable_omegaLower]

@[simp] theorem MUpper_dirac (a : Param) : MUpper (diracRaw a) = omegaUpper a := by
  change (∫⁻ x, omegaUpper x ∂Measure.dirac a) = omegaUpper a
  rw [lintegral_dirac' a measurable_omegaUpper]

theorem omegaLower_lt_top (a : Param) : omegaLower a < ⊤ := by
  unfold omegaLower
  split_ifs
  · exact ENNReal.ofReal_lt_top
  · exact ENNReal.zero_lt_top

theorem omegaUpper_lt_top (a : Param) : omegaUpper a < ⊤ := by
  unfold omegaUpper
  split_ifs
  · exact ENNReal.ofReal_lt_top
  · exact ENNReal.zero_lt_top

theorem MomFin_dirac (a : Param) : MomFin (diracRaw a) := by
  exact ⟨by simpa using omegaLower_lt_top a, by simpa using omegaUpper_lt_top a⟩

/-- Positive finite-temperature admissibility. -/
def PosAdm (t : ℝ) (τ : ProbabilityMeasure Param) : Prop :=
  0 < t ∧
    suppMeasure (probMeasure τ) ⊆ Set.Icc (0 : Param) 1 ∧
    probMeasure τ {1} = 0 ∧
    MLower (probMeasure τ) ≤ ENNReal.ofReal (1 / t)

/-- Negative finite-temperature admissibility with lower support only. -/
def NegLowerAdm (t : ℝ) (τ : ProbabilityMeasure Param) : Prop :=
  t < 0 ∧ suppMeasure (probMeasure τ) ⊆ Set.Icc (0 : Param) 1

/-- Exceptional negative finite-temperature admissibility. -/
def NegExcAdm (t : ℝ) (τ : ProbabilityMeasure Param) (astar : Param) : Prop :=
  t < 0 ∧ 1 < astar ∧
    suppMeasure (probMeasure τ) ⊆ Set.Icc (0 : Param) 1 ∪ {astar} ∧
    probMeasure τ {1} = 0 ∧
    MLower (probMeasure τ) < ⊤ ∧
    MomFin (probMeasure τ) ∧
    MReal (probMeasure τ) ≤ 1 / t

/-- Exceptional negative tropical admissibility. -/
def NegTropExcAdm (τ : ProbabilityMeasure Param) (astar : Param) : Prop :=
  1 < astar ∧
    suppMeasure (probMeasure τ) ⊆ Set.Icc (0 : Param) 1 ∪ {astar} ∧
    probMeasure τ {1} = 0 ∧
    MLower (probMeasure τ) < ⊤ ∧
    MomFin (probMeasure τ) ∧
    MReal (probMeasure τ) ≤ 0

/-- Complete finite-temperature parameter predicate. -/
def DBulk (t : ℝ) (τ : ProbabilityMeasure Param) : Prop :=
  PosAdm t τ ∨ NegLowerAdm t τ ∨ ∃ astar, NegExcAdm t τ astar

namespace DBulk

theorem ne {t : ℝ} {τ : ProbabilityMeasure Param} (h : DBulk t τ) : t ≠ 0 := by
  rcases h with hp | hn | he
  · exact ne_of_gt hp.1
  · exact ne_of_lt hn.1
  · rcases he with ⟨astar, he⟩
    exact ne_of_lt he.1

end DBulk

/-- Complete negative-tropical parameter predicate. -/
def DMinus (τ : ProbabilityMeasure Param) : Prop :=
  suppMeasure (probMeasure τ) ⊆ Set.Icc (0 : Param) 1 ∨
    ∃ astar, NegTropExcAdm τ astar

end ConditionalEntropy
