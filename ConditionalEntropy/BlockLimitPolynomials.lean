import ConditionalEntropy.SpecialBlockData

/-!
# Explicit two- and three-block localization targets

These are the scalar polynomials obtained after integrating the piecewise
constant block-limit kernels.  They are total definitions; the separate
limit-passage module proves that the finite block kernels converge to them.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

/-! ## Two-block targets -/

def twoUpperLogFirst (mu : SignedMeasure Param) (r : ℝ) (u : Fin 2 → ℝ) : ℝ :=
  let A := upperMoment mu r
  (1 - A) * u 0 + A * u 1

def twoUpperLogSecond (mu : SignedMeasure Param) (r : ℝ) (u : Fin 2 → ℝ) : ℝ :=
  let A := upperMoment mu r
  (-(1 - A) * (u 0) ^ 2 - A * (u 1) ^ 2)

def twoLowerLogFirst (mu : SignedMeasure Param) (r : ℝ) (u : Fin 2 → ℝ) : ℝ :=
  let A := lowerMoment mu r
  A * u 0 + (1 - A) * u 1

def twoLowerLogSecond (mu : SignedMeasure Param) (r : ℝ) (u : Fin 2 → ℝ) : ℝ :=
  let A := lowerMoment mu r
  (-A * (u 0) ^ 2 - (1 - A) * (u 1) ^ 2)

def twoUpperGFirst (mu : SignedMeasure Param) (r : ℝ) (u : Fin 2 → ℝ) : ℝ :=
  let A := upperMoment mu r
  A * (u 1 - u 0)

def twoUpperGSecond (mu : SignedMeasure Param) (r : ℝ) (u : Fin 2 → ℝ) : ℝ :=
  let A := upperMoment mu r
  A * ((u 0) ^ 2 - (u 1) ^ 2)

def twoLowerGFirst (mu : SignedMeasure Param) (r : ℝ) (u : Fin 2 → ℝ) : ℝ :=
  let A := lowerMoment mu r
  A * (u 0 - u 1)

def twoLowerGSecond (mu : SignedMeasure Param) (r : ℝ) (u : Fin 2 → ℝ) : ℝ :=
  let A := lowerMoment mu r
  A * ((u 1) ^ 2 - (u 0) ^ 2)

/-! ## Three-block targets -/

/-- Signed singular-weight masses of the three strict dominance cells. -/
def threeCellMoment (mu : SignedMeasure Param) (a b : ℝ) : Fin 3 → ℝ :=
  ![signedIntegral mu ((Iio (finiteParam a)).indicator singularWeight),
    signedIntegral mu
      ((Ioo (finiteParam a) (finiteParam b)).indicator singularWeight),
    signedIntegral mu ((Ioi (finiteParam b)).indicator singularWeight)]

def threeLogFirst (mu : SignedMeasure Param) (a b : ℝ)
    (u : Fin 3 → ℝ) : ℝ :=
  let k := threeNormBlock a b
  u k + ∑ j ∈ Finset.univ.erase k,
    threeCellMoment mu a b j * (u j - u k)

def threeLogSecond (mu : SignedMeasure Param) (a b : ℝ)
    (u : Fin 3 → ℝ) : ℝ :=
  let k := threeNormBlock a b
  (-(u k) ^ 2 + ∑ j ∈ Finset.univ.erase k,
    threeCellMoment mu a b j * ((u k) ^ 2 - (u j) ^ 2))

def threeGFirst (mu : SignedMeasure Param) (a b : ℝ)
    (u : Fin 3 → ℝ) : ℝ :=
  let k := threeNormBlock a b
  ∑ j ∈ Finset.univ.erase k,
    threeCellMoment mu a b j * (u j - u k)

def threeGSecond (mu : SignedMeasure Param) (a b : ℝ)
    (u : Fin 3 → ℝ) : ℝ :=
  let k := threeNormBlock a b
  ∑ j ∈ Finset.univ.erase k,
    threeCellMoment mu a b j * ((u k) ^ 2 - (u j) ^ 2)

/-! ## Elementary algebra and regularity -/

theorem twoUpperLogFirst_eq_mass_add_g (mu : SignedMeasure Param) (r : ℝ)
    (u : Fin 2 → ℝ) :
    twoUpperLogFirst mu r u = u 0 + twoUpperGFirst mu r u := by
  simp [twoUpperLogFirst, twoUpperGFirst]
  ring

theorem twoUpperLogSecond_eq_mass_add_g (mu : SignedMeasure Param) (r : ℝ)
    (u : Fin 2 → ℝ) :
    twoUpperLogSecond mu r u = -(u 0) ^ 2 + twoUpperGSecond mu r u := by
  simp [twoUpperLogSecond, twoUpperGSecond]
  ring

theorem twoLowerLogFirst_eq_mass_add_g (mu : SignedMeasure Param) (r : ℝ)
    (u : Fin 2 → ℝ) :
    twoLowerLogFirst mu r u = u 1 + twoLowerGFirst mu r u := by
  simp [twoLowerLogFirst, twoLowerGFirst]
  ring

theorem twoLowerLogSecond_eq_mass_add_g (mu : SignedMeasure Param) (r : ℝ)
    (u : Fin 2 → ℝ) :
    twoLowerLogSecond mu r u = -(u 1) ^ 2 + twoLowerGSecond mu r u := by
  simp [twoLowerLogSecond, twoLowerGSecond]
  ring

theorem threeLogFirst_eq_mass_add_g (mu : SignedMeasure Param) (a b : ℝ)
    (u : Fin 3 → ℝ) :
    threeLogFirst mu a b u =
      u (threeNormBlock a b) + threeGFirst mu a b u := by
  rfl

theorem threeLogSecond_eq_mass_add_g (mu : SignedMeasure Param) (a b : ℝ)
    (u : Fin 3 → ℝ) :
    threeLogSecond mu a b u =
      -(u (threeNormBlock a b)) ^ 2 + threeGSecond mu a b u := by
  simp [threeLogSecond, threeGSecond]

theorem continuous_twoUpperGFirst (mu : SignedMeasure Param) (r : ℝ) :
    Continuous (twoUpperGFirst mu r) := by
  unfold twoUpperGFirst
  fun_prop

theorem continuous_twoUpperGSecond (mu : SignedMeasure Param) (r : ℝ) :
    Continuous (twoUpperGSecond mu r) := by
  unfold twoUpperGSecond
  fun_prop

theorem continuous_twoLowerGFirst (mu : SignedMeasure Param) (r : ℝ) :
    Continuous (twoLowerGFirst mu r) := by
  unfold twoLowerGFirst
  fun_prop

theorem continuous_twoLowerGSecond (mu : SignedMeasure Param) (r : ℝ) :
    Continuous (twoLowerGSecond mu r) := by
  unfold twoLowerGSecond
  fun_prop

theorem continuous_threeGFirst (mu : SignedMeasure Param) (a b : ℝ) :
    Continuous (threeGFirst mu a b) := by
  unfold threeGFirst
  fun_prop

theorem continuous_threeGSecond (mu : SignedMeasure Param) (a b : ℝ) :
    Continuous (threeGSecond mu a b) := by
  unfold threeGSecond
  fun_prop

end ConditionalEntropy
