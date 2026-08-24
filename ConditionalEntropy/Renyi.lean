import ConditionalEntropy.FiniteData
import ConditionalEntropy.ParamMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Endpoint-aware finite Renyi entropy

The order parameter is the compactified type `Param = WithTop NNReal`.  The
definition is total at orders `0`, `1`, and `+infinity`; finite nonendpoint
orders use the ordinary real-power formula.
-/

noncomputable section

open Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u v

section

variable {I : Type u} [Fintype I] [Nonempty I]

/-- The finite power sum of a probability vector. -/
def powerSum (a : ℝ) (p : ProbVec I) : ℝ :=
  ∑ i, p.1 i ^ a

/-- Hartley entropy (order zero). -/
def renyiZero (p : ProbVec I) : ℝ :=
  Real.log (supportFinset p.1).card

/-- Shannon entropy, with Mathlib's total convention `log 0 = 0`. -/
def renyiOne (p : ProbVec I) : ℝ :=
  -∑ i, p.1 i * Real.log (p.1 i)

/-- Min-entropy (order `+infinity`). -/
def renyiTop (p : ProbVec I) : ℝ :=
  -Real.log (finMax p.1)

/-- The ordinary finite-order formula away from orders zero and one. -/
def renyiFinite (a : ℝ) (p : ProbVec I) : ℝ :=
  Real.log (powerSum a p) / (1 - a)

/-- Total endpoint-aware Renyi entropy. -/
def renyi (a : Param) (p : ProbVec I) : ℝ :=
  if htop : a = ⊤ then renyiTop p
  else if _hzero : a = 0 then renyiZero p
  else if _hone : a = 1 then renyiOne p
  else renyiFinite (paramToReal a htop) p

@[simp] theorem renyi_at_top (p : ProbVec I) : renyi (⊤ : Param) p = renyiTop p := by
  simp [renyi]

@[simp] theorem renyi_at_zero (p : ProbVec I) : renyi (0 : Param) p = renyiZero p := by
  simp [renyi]

@[simp] theorem renyi_at_one (p : ProbVec I) : renyi (1 : Param) p = renyiOne p := by
  simp [renyi]

theorem renyi_finite {a : ℝ} (ha : 0 ≤ a) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (p : ProbVec I) :
    renyi (finiteParam a) p = renyiFinite a p := by
  have htop := finiteParam_ne_top a
  have hzero : finiteParam a ≠ (0 : Param) := by
    intro h
    exact ha0 ((finiteParam_eq_zero_iff.mp h).antisymm ha)
  have hone : finiteParam a ≠ (1 : Param) := by
    intro h
    apply ha1
    apply finiteParam_injectiveOn_nonneg ha (by norm_num)
    simpa using h
  simp [renyi, htop, hzero, hone, paramToReal_finiteParam ha]

omit [Nonempty I] in
theorem exists_prob_pos (p : ProbVec I) : ∃ i, 0 < p.1 i := by
  by_contra h
  push Not at h
  have hpzero : p.1 = 0 := by
    funext i
    exact le_antisymm (h i) (p.2.1 i)
  have hmass := p.2.2
  rw [hpzero] at hmass
  simp [l1Mass] at hmass

omit [Nonempty I] in
theorem powerSum_pos {a : ℝ} (_ha : 0 < a) (p : ProbVec I) :
    0 < powerSum a p := by
  obtain ⟨i, hi⟩ := exists_prob_pos p
  apply Finset.sum_pos'
  · intro j _
    exact Real.rpow_nonneg (p.2.1 j) _
  · exact ⟨i, Finset.mem_univ i, Real.rpow_pos_of_pos hi _⟩

omit [Nonempty I] in
theorem powerSum_nonneg (a : ℝ) (p : ProbVec I) :
    0 ≤ powerSum a p := by
  exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (p.2.1 i) _

omit [Nonempty I] in
@[simp] theorem powerSum_one (p : ProbVec I) : powerSum 1 p = 1 := by
  have hp : ∑ i, p.1 i = 1 := by simpa only [l1Mass] using p.2.2
  simpa [powerSum] using hp

omit [Nonempty I] in
theorem powerSum_tensor {J : Type v} [Fintype J]
    (a : ℝ) (p : ProbVec I) (q : ProbVec J) :
    powerSum a (probTensor p q) = powerSum a p * powerSum a q := by
  simp only [powerSum, probTensor, Fintype.sum_prod_type]
  simp_rw [Real.mul_rpow (p.2.1 _) (q.2.1 _)]
  exact (Fintype.sum_mul_sum (fun i => p.1 i ^ a) (fun j => q.1 j ^ a)).symm

end

end ConditionalEntropy
