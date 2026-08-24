import ConditionalEntropy.IntegratedEntropy
import ConditionalEntropy.LineData

/-!
# Conditional-entropy column functions

This module gives the total perspective-style column functions used by the
shape reductions.  Every zero column is handled by an explicit branch, and
every normalization of a nonzero column is proof carrying.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace ConditionalEntropy

universe u v

/-- Invariance of a function on the punctured cone under positive scaling. -/
def ScaleInvariant {I : Type u} (f : PosConeVec I → ℝ) : Prop :=
  ∀ x : PosConeVec I, ∀ c : ℝ, ∀ hc : 0 < c,
    f (posScale c hc x) = f x

/-- The maximum-reversing curvature predicate needed by the positive tropical
candidate. -/
def MaxQCave {I : Type u} (f : PosConeVec I → ℝ) : Prop :=
  ∀ x z : PosConeVec I, ∀ lambda : ℝ,
    ∀ hlambda : 0 < lambda ∧ lambda < 1,
      max (f x) (f z) ≤ f (posMix lambda hlambda x z)

/-- Total exponential perspective of the integrated entropy. -/
def columnPhi {I : Type u} [Fintype I] [Nonempty I]
    (t : ℝ) (τ : ProbabilityMeasure Param) (x : ConeVec I) : ℝ :=
  if hx : x = 0 then 0
  else l1Mass x.1 * Real.exp
    (t * integratedEntropyPos (probMeasure τ) (normalize (toPosCone x hx)))

/-- Total linear perspective of the integrated entropy. -/
def columnDeriv {I : Type u} [Fintype I] [Nonempty I]
    (σ : FiniteMeasure Param) (x : ConeVec I) : ℝ :=
  if hx : x = 0 then 0
  else l1Mass x.1 *
    integratedEntropyPos (finiteMeasure σ) (normalize (toPosCone x hx))

/-- Positive-tropical column functional. -/
def aTrop {I : Type u} [Fintype I] [Nonempty I]
    (τ : ProbabilityMeasure Param) (x : PosConeVec I) : ℝ :=
  integratedEntropyPos (probMeasure τ) (normalize x)

/-- Negative-tropical column functional. -/
def gTrop {I : Type u} [Fintype I] [Nonempty I]
    (τ : ProbabilityMeasure Param) (x : PosConeVec I) : ℝ :=
  -aTrop τ x

@[simp] theorem columnPhi_zero {I : Type u} [Fintype I] [Nonempty I]
    (t : ℝ) (τ : ProbabilityMeasure Param) :
    columnPhi t τ (0 : ConeVec I) = 0 := by
  simp [columnPhi]

@[simp] theorem columnDeriv_zero {I : Type u} [Fintype I] [Nonempty I]
    (σ : FiniteMeasure Param) :
    columnDeriv σ (0 : ConeVec I) = 0 := by
  simp [columnDeriv]

theorem columnPhi_of_ne {I : Type u} [Fintype I] [Nonempty I]
    (t : ℝ) (τ : ProbabilityMeasure Param) (x : ConeVec I) (hx : x ≠ 0) :
    columnPhi t τ x = l1Mass x.1 * Real.exp
      (t * integratedEntropyPos (probMeasure τ)
        (normalize (toPosCone x hx))) := by
  simp [columnPhi, hx]

theorem columnDeriv_of_ne {I : Type u} [Fintype I] [Nonempty I]
    (σ : FiniteMeasure Param) (x : ConeVec I) (hx : x ≠ 0) :
    columnDeriv σ x = l1Mass x.1 *
      integratedEntropyPos (finiteMeasure σ)
        (normalize (toPosCone x hx)) := by
  simp [columnDeriv, hx]

/-- The proof-carrying positive scale of a nonzero cone vector is the same
subtype as scaling its punctured-cone bundle. -/
theorem toPosCone_coneScale {I : Type u}
    (c : ℝ) (hc : 0 < c) (x : ConeVec I) (hx : x ≠ 0) :
    toPosCone (coneScale c hc.le x) (by
      intro hzero
      have hval := congrArg (fun z : ConeVec I => z.1) hzero
      apply hx
      apply Subtype.ext
      funext i
      have hi : c * x.1 i = 0 := congrFun hval i
      exact (mul_eq_zero.mp hi).resolve_left hc.ne') =
      posScale c hc (toPosCone x hx) := by
  rfl

/-- The exponential column perspective is positively homogeneous of degree
one, including the zero scalar and zero vector branches. -/
theorem columnPhi_posHomOne {I : Type u} [Fintype I] [Nonempty I]
    (t : ℝ) (τ : ProbabilityMeasure Param) :
    PosHomOne (columnPhi t τ : ConeVec I → ℝ) := by
  intro x c hc
  rcases hc.eq_or_lt with rfl | hcpos
  · have hzero : coneScale 0 (le_refl 0) x = 0 := by
      apply Subtype.ext
      funext i
      simp [coneScale]
    rw [hzero, columnPhi_zero]
    ring
  by_cases hx : x = 0
  · have hscaled : coneScale c hcpos.le x = 0 := by
      subst x
      apply Subtype.ext
      funext i
      simp [coneScale]
    rw [hscaled, columnPhi_zero, hx, columnPhi_zero]
    ring
  · have hscaled : coneScale c hcpos.le x ≠ 0 := by
      intro hzero
      have hval := congrArg (fun z : ConeVec I => z.1) hzero
      apply hx
      apply Subtype.ext
      funext i
      have hi : c * x.1 i = 0 := congrFun hval i
      exact (mul_eq_zero.mp hi).resolve_left hcpos.ne'
    rw [columnPhi_of_ne t τ _ hscaled, columnPhi_of_ne t τ x hx,
      l1Mass_coneScale]
    rw [toPosCone_coneScale c hcpos x hx, normalize_posScale]
    ring

/-- The derivation column perspective is positively homogeneous of degree
one. -/
theorem columnDeriv_posHomOne {I : Type u} [Fintype I] [Nonempty I]
    (σ : FiniteMeasure Param) :
    PosHomOne (columnDeriv σ : ConeVec I → ℝ) := by
  intro x c hc
  rcases hc.eq_or_lt with rfl | hcpos
  · have hzero : coneScale 0 (le_refl 0) x = 0 := by
      apply Subtype.ext
      funext i
      simp [coneScale]
    rw [hzero, columnDeriv_zero]
    ring
  by_cases hx : x = 0
  · have hscaled : coneScale c hcpos.le x = 0 := by
      subst x
      apply Subtype.ext
      funext i
      simp [coneScale]
    rw [hscaled, columnDeriv_zero, hx, columnDeriv_zero]
    ring
  · have hscaled : coneScale c hcpos.le x ≠ 0 := by
      intro hzero
      have hval := congrArg (fun z : ConeVec I => z.1) hzero
      apply hx
      apply Subtype.ext
      funext i
      have hi : c * x.1 i = 0 := congrFun hval i
      exact (mul_eq_zero.mp hi).resolve_left hcpos.ne'
    rw [columnDeriv_of_ne σ _ hscaled, columnDeriv_of_ne σ x hx,
      l1Mass_coneScale]
    rw [toPosCone_coneScale c hcpos x hx, normalize_posScale]
    ring

theorem aTrop_scaleInvariant {I : Type u} [Fintype I] [Nonempty I]
    (τ : ProbabilityMeasure Param) :
    ScaleInvariant (aTrop τ : PosConeVec I → ℝ) := by
  intro x c hc
  simp only [aTrop, normalize_posScale]

theorem gTrop_scaleInvariant {I : Type u} [Fintype I] [Nonempty I]
    (τ : ProbabilityMeasure Param) :
    ScaleInvariant (gTrop τ : PosConeVec I → ℝ) := by
  intro x c hc
  simp only [gTrop, aTrop, normalize_posScale]

/-- On an active joint column, the total exponential perspective reduces to
the conditional probability formula. -/
theorem columnPhi_active {I : Type u} {J : Type v}
    [Fintype I] [Nonempty I] [Fintype J]
    (t : ℝ) (τ : ProbabilityMeasure Param) (P : JointProb I J)
    (y : Active P) :
    columnPhi t τ (column P y.1) = colMass P y.1 * Real.exp
      (t * integratedEntropyPos (probMeasure τ) (conditional P y)) := by
  rw [columnPhi_of_ne t τ _ (active_column_ne_zero P y)]
  rfl

/-- On an active joint column, the linear perspective reduces to the
conditional probability formula. -/
theorem columnDeriv_active {I : Type u} {J : Type v}
    [Fintype I] [Nonempty I] [Fintype J]
    (σ : FiniteMeasure Param) (P : JointProb I J) (y : Active P) :
    columnDeriv σ (column P y.1) = colMass P y.1 *
      integratedEntropyPos (finiteMeasure σ) (conditional P y) := by
  rw [columnDeriv_of_ne σ _ (active_column_ne_zero P y)]
  rfl

/-- A non-active column is the zero cone vector. -/
theorem column_eq_zero_of_not_active {I : Type u} {J : Type v}
    [Fintype I] [Fintype J] (P : JointProb I J) (y : J)
    (hy : y ∉ activeFinset P) :
    column P y = 0 := by
  have hnonneg : 0 ≤ colMass P y :=
    Finset.sum_nonneg fun i _ => P.2.1 i y
  have hnpos : ¬ 0 < colMass P y := by
    simpa [activeFinset] using hy
  by_contra hne
  exact hnpos ((coneNonzeroMass (column P y)).mp hne)

/-- Summing the exponential perspective over all columns deletes precisely the
zero columns and gives the active-column exponential sum. -/
theorem sum_columnPhi_eq_temperateSum {I J : Type u}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (t : ℝ) (τ : ProbabilityMeasure Param) (P : JointProb I J) :
    (∑ y : J, columnPhi t τ (column P y)) = temperateSum t τ P := by
  classical
  letI : Fintype (Active P) :=
    Fintype.ofFinset (activeFinset P) fun _ => Iff.rfl
  calc
    (∑ y : J, columnPhi t τ (column P y)) =
        ∑ y ∈ activeFinset P, columnPhi t τ (column P y) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ hy
      rw [column_eq_zero_of_not_active P y hy, columnPhi_zero]
    _ = ∑ y : Active P, columnPhi t τ (column P y.1) := by
      exact Finset.sum_subtype (activeFinset P) (fun _ => Iff.rfl)
        (fun y => columnPhi t τ (column P y))
    _ = ∑ y : Active P, colMass P y.1 * Real.exp
        (t * integratedEntropyPos (probMeasure τ) (conditional P y)) := by
      apply Finset.sum_congr rfl
      intro y _
      exact columnPhi_active t τ P y
    _ = temperateSum t τ P := rfl

/-- The manuscript's exponential identity for the finite-temperature
candidate. -/
theorem sum_columnPhi_eq_exp_HTemp {I J : Type u}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (t : ℝ) (ht : t ≠ 0) (τ : ProbabilityMeasure Param)
    (P : JointProb I J) :
    (∑ y : J, columnPhi t τ (column P y)) =
      Real.exp (t * HTemp t ht τ P) := by
  rw [sum_columnPhi_eq_temperateSum]
  change temperateSum t τ P =
    Real.exp (t * (Real.log (temperateSum t τ P) / t))
  have halg : t * (Real.log (temperateSum t τ P) / t) =
      Real.log (temperateSum t τ P) := by
    field_simp
  rw [halg]
  exact (Real.exp_log (temperateSum_pos t τ P)).symm

/-- Summing the linear perspective over all columns is exactly the derivation
candidate. -/
theorem sum_columnDeriv_eq_HZero {I J : Type u}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (σ : FiniteMeasure Param) (P : JointProb I J) :
    (∑ y : J, columnDeriv σ (column P y)) = HZero σ P := by
  classical
  letI : Fintype (Active P) :=
    Fintype.ofFinset (activeFinset P) fun _ => Iff.rfl
  calc
    (∑ y : J, columnDeriv σ (column P y)) =
        ∑ y ∈ activeFinset P, columnDeriv σ (column P y) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ hy
      rw [column_eq_zero_of_not_active P y hy, columnDeriv_zero]
    _ = ∑ y : Active P, columnDeriv σ (column P y.1) := by
      exact Finset.sum_subtype (activeFinset P) (fun _ => Iff.rfl)
        (fun y => columnDeriv σ (column P y))
    _ = ∑ y : Active P, colMass P y.1 *
        integratedEntropyPos (finiteMeasure σ) (conditional P y) := by
      apply Finset.sum_congr rfl
      intro y _
      exact columnDeriv_active σ P y
    _ = HZero σ P := rfl

/-- Literal column-identity and homogeneity package used by the shape
reductions. -/
theorem columnIdentities {I J : Type u}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J] :
    (∀ (τ : ProbabilityMeasure Param) (t : ℝ),
      PosHomOne (columnPhi t τ : ConeVec I → ℝ) ∧
      ScaleInvariant (aTrop τ : PosConeVec I → ℝ) ∧
      ScaleInvariant (gTrop τ : PosConeVec I → ℝ) ∧
      ∀ (ht : t ≠ 0) (P : JointProb I J),
        (∑ y : J, columnPhi t τ (column P y)) =
          Real.exp (t * HTemp t ht τ P)) ∧
    (∀ σ : FiniteMeasure Param,
      PosHomOne (columnDeriv σ : ConeVec I → ℝ) ∧
      ∀ P : JointProb I J,
        (∑ y : J, columnDeriv σ (column P y)) = HZero σ P) := by
  constructor
  · intro τ t
    exact ⟨columnPhi_posHomOne t τ, aTrop_scaleInvariant τ,
      gTrop_scaleInvariant τ, fun ht P => sum_columnPhi_eq_exp_HTemp t ht τ P⟩
  · intro σ
    exact ⟨columnDeriv_posHomOne σ, fun P => sum_columnDeriv_eq_HZero σ P⟩

end ConditionalEntropy
