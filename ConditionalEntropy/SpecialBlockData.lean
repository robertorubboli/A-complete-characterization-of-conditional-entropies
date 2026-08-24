import ConditionalEntropy.BlockEstimates
import ConditionalEntropy.CompactUniform
import ConditionalEntropy.Moments

/-!
# Specialized two- and three-block data

These are the total finite block families and dominance maps used by the
localization argument.  Threshold equality is assigned to the block on its
right, and the compactified top order is assigned to the final block.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Topology

namespace ConditionalEntropy

/-- Two-block exponents and amplitudes with crossing at `r`. -/
def twoBlockData (r R : ℝ) (hr : 0 < r) (hR : r < R) : BlockData 1 where
  m := ![R, R - r]
  m_pos := by
    intro i
    fin_cases i <;> simp <;> linarith
  a := ![0, 1]

/-- Three-block exponents and amplitudes with crossings at `a` and `b`. -/
def threeBlockData (a b R : ℝ) (ha : 0 < a) (hab : a < b)
    (hR : a + b < R) : BlockData 2 where
  m := ![R, R - a, R - a - b]
  m_pos := by
    intro i
    fin_cases i <;> simp <;> linarith
  a := ![0, 1, 2]

/-- Signed lower truncation of the singular coefficient. -/
def lowerMoment (mu : SignedMeasure Param) (r : ℝ) : ℝ :=
  signedIntegral mu ((Iio (finiteParam r)).indicator singularWeight)

/-- Signed upper truncation of the singular coefficient. -/
def upperMoment (mu : SignedMeasure Param) (r : ℝ) : ℝ :=
  signedIntegral mu ((Ioi (finiteParam r)).indicator singularWeight)

/-- The last amplitude is uniquely largest in the two-block family. -/
theorem twoBlockTopUnique (r R : ℝ) (hr : 0 < r) (hR : r < R) :
    ∀ j : Fin 2, j ≠ 1 →
      (twoBlockData r R hr hR).a j < (twoBlockData r R hr hR).a 1 := by
  intro j hj
  fin_cases j <;> simp_all [twoBlockData]

/-- The last amplitude is uniquely largest in the three-block family. -/
theorem threeBlockTopUnique (a b R : ℝ) (ha : 0 < a) (hab : a < b)
    (hR : a + b < R) :
    ∀ j : Fin 3, j ≠ 2 →
      (threeBlockData a b R ha hab hR).a j <
        (threeBlockData a b R ha hab hR).a 2 := by
  intro j hj
  fin_cases j <;> simp_all [threeBlockData]

/-- Block dominating the order-one norm in a three-block family. -/
def threeNormBlock (a b : ℝ) : Fin 3 :=
  if 1 < a then 0 else if 1 < b then 1 else 2

/-- Total two-block dominance map. -/
def twoDominanceMap (r : ℝ) (beta : Param) : Fin 2 :=
  if beta < finiteParam r then 0 else 1

/-- Total three-block dominance map. -/
def threeDominanceMap (a b : ℝ) (beta : Param) : Fin 3 :=
  if beta < finiteParam a then 0
  else if beta < finiteParam b then 1 else 2

theorem measurable_twoDominanceMap (r : ℝ) : Measurable (twoDominanceMap r) := by
  unfold twoDominanceMap
  exact Measurable.ite measurableSet_Iio measurable_const measurable_const

theorem measurable_threeDominanceMap (a b : ℝ) :
    Measurable (threeDominanceMap a b) := by
  unfold threeDominanceMap
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)

@[simp] theorem twoDominanceMap_top (r : ℝ) :
    twoDominanceMap r ⊤ = 1 := by
  simp [twoDominanceMap]

@[simp] theorem threeDominanceMap_top (a b : ℝ) :
    threeDominanceMap a b ⊤ = 2 := by
  simp [threeDominanceMap]

/-- Exact measurability, endpoint value, and strict dominance package for the
two-block family. -/
theorem twoBlockDominancePackage (r R : ℝ) (hr : 0 < r) (hR : r < R) :
    let B := twoBlockData r R hr hR
    let k := twoDominanceMap r
    Measurable k ∧ k ⊤ = 1 ∧
      ∀ alpha : ℝ, 0 ≤ alpha → alpha ∉ ({r} : Finset ℝ) →
        ∀ j : Fin 2, j ≠ k (finiteParam alpha) →
          blockExponent B j alpha <
            blockExponent B (k (finiteParam alpha)) alpha := by
  dsimp only
  refine ⟨measurable_twoDominanceMap r, twoDominanceMap_top r, ?_⟩
  intro alpha halpha hnot j hj
  have hne : alpha ≠ r := by simpa using hnot
  have hcmp : finiteParam alpha < finiteParam r ↔ alpha < r := by
    change ENNReal.ofReal alpha < ENNReal.ofReal r ↔ alpha < r
    exact ENNReal.ofReal_lt_ofReal_iff hr
  by_cases har : alpha < r
  · have hk : twoDominanceMap r (finiteParam alpha) = 0 := by
      simp [twoDominanceMap, hcmp.mpr har]
    rw [hk] at hj ⊢
    fin_cases j
    · simp at hj
    · simp [twoBlockData, blockExponent]
      linarith
  · have hra : r < alpha := lt_of_le_of_ne (not_lt.mp har) hne.symm
    have hk : twoDominanceMap r (finiteParam alpha) = 1 := by
      simp [twoDominanceMap, hcmp, har]
    rw [hk] at hj ⊢
    fin_cases j
    · simp [twoBlockData, blockExponent]
      linarith
    · simp at hj

/-- Exact measurability, endpoint value, and strict dominance package for the
three-block family. -/
theorem threeBlockDominancePackage (a b R : ℝ) (ha : 0 < a) (hab : a < b)
    (hR : a + b < R) :
    let B := threeBlockData a b R ha hab hR
    let k := threeDominanceMap a b
    Measurable k ∧ k ⊤ = 2 ∧
      ∀ alpha : ℝ, 0 ≤ alpha → alpha ∉ ({a, b} : Finset ℝ) →
        ∀ j : Fin 3, j ≠ k (finiteParam alpha) →
          blockExponent B j alpha <
            blockExponent B (k (finiteParam alpha)) alpha := by
  dsimp only
  refine ⟨measurable_threeDominanceMap a b,
    threeDominanceMap_top a b, ?_⟩
  intro alpha halpha hnot j hj
  have hb : 0 < b := ha.trans hab
  have hneA : alpha ≠ a := by
    intro heq
    apply hnot
    simp [heq]
  have hneB : alpha ≠ b := by
    intro heq
    apply hnot
    simp [heq]
  have hcmpA : finiteParam alpha < finiteParam a ↔ alpha < a := by
    change ENNReal.ofReal alpha < ENNReal.ofReal a ↔ alpha < a
    exact ENNReal.ofReal_lt_ofReal_iff ha
  have hcmpB : finiteParam alpha < finiteParam b ↔ alpha < b := by
    change ENNReal.ofReal alpha < ENNReal.ofReal b ↔ alpha < b
    exact ENNReal.ofReal_lt_ofReal_iff hb
  by_cases hAlphaA : alpha < a
  · have hk : threeDominanceMap a b (finiteParam alpha) = 0 := by
      simp [threeDominanceMap, hcmpA.mpr hAlphaA]
    rw [hk] at hj ⊢
    fin_cases j <;> simp_all [threeBlockData, blockExponent] <;> linarith
  · have haAlpha : a < alpha := lt_of_le_of_ne (not_lt.mp hAlphaA) hneA.symm
    by_cases hAlphaB : alpha < b
    · have hk : threeDominanceMap a b (finiteParam alpha) = 1 := by
        simp [threeDominanceMap, hcmpA, hcmpB, hAlphaA, hAlphaB]
      rw [hk] at hj ⊢
      fin_cases j <;> simp_all [threeBlockData, blockExponent] <;> linarith
    · have hbAlpha : b < alpha := lt_of_le_of_ne (not_lt.mp hAlphaB) hneB.symm
      have hk : threeDominanceMap a b (finiteParam alpha) = 2 := by
        simp [threeDominanceMap, hcmpA, hcmpB, hAlphaA, hAlphaB]
      rw [hk] at hj ⊢
      fin_cases j <;> simp_all [threeBlockData, blockExponent] <;> linarith

/-- Unique order-one dominant block in the two-block family. -/
theorem twoOrderOneDominancePackage (r R : ℝ) (hr : 0 < r) (hR : r < R) :
    let B := twoBlockData r R hr hR
    (1 < r → ∀ j : Fin 2, j ≠ 0 →
      blockExponent B j 1 < blockExponent B 0 1) ∧
    (r < 1 → ∀ j : Fin 2, j ≠ 1 →
      blockExponent B j 1 < blockExponent B 1 1) := by
  dsimp only
  constructor
  · intro hr1 j hj
    fin_cases j
    · simp at hj
    · simp [twoBlockData, blockExponent]
      linarith
  · intro h1r j hj
    fin_cases j
    · simp [twoBlockData, blockExponent]
      linarith
    · simp at hj

/-- Unique order-one dominant block in the three-block family. -/
theorem threeOrderOneDominant (a b R : ℝ) (ha : 0 < a) (hab : a < b)
    (hR : a + b < R) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    let B := threeBlockData a b R ha hab hR
    ∀ j : Fin 3, j ≠ threeNormBlock a b →
      blockExponent B j 1 <
        blockExponent B (threeNormBlock a b) 1 := by
  dsimp only
  by_cases h1a : 1 < a
  · have hk : threeNormBlock a b = 0 := by simp [threeNormBlock, h1a]
    rw [hk]
    intro j hj
    fin_cases j <;> simp_all [threeBlockData, blockExponent] <;> linarith
  · have haLe : a < 1 := lt_of_le_of_ne (not_lt.mp h1a) ha1
    by_cases h1b : 1 < b
    · have hk : threeNormBlock a b = 1 := by
        simp [threeNormBlock, h1a, h1b]
      rw [hk]
      intro j hj
      fin_cases j <;> simp_all [threeBlockData, blockExponent] <;> linarith
    · have hbLe : b < 1 := lt_of_le_of_ne (not_lt.mp h1b) hb1
      have hk : threeNormBlock a b = 2 := by
        simp [threeNormBlock, h1a, h1b]
      rw [hk]
      intro j hj
      fin_cases j <;> simp_all [threeBlockData, blockExponent] <;> linarith

end ConditionalEntropy
