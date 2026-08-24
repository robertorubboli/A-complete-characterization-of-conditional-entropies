import ConditionalEntropy.Cone
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Order

/-!
# Finite probability and joint-probability data

This module implements the proof-carrying finite carriers used by the
conditional-entropy classification.  All normalizations are guarded by a
proof of nonzeroness; zero columns are never normalized.
-/

open scoped BigOperators
open Set

namespace ConditionalEntropy

universe u v w u' v'

section Vectors

variable {I : Type u} [Fintype I]

/-- The total mass of a finite real vector. -/
noncomputable def l1Mass (x : I → ℝ) : ℝ :=
  ∑ i, x i

/-- The finite support of a vector. -/
noncomputable def supportFinset (x : I → ℝ) : Finset I :=
  Finset.univ.filter fun i => x i ≠ 0

/-- The minimum of a real family on a finite nonempty type. -/
noncomputable def finMin [Nonempty I] (a : I → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty a

/-- The maximum of a real family on a finite nonempty type. -/
noncomputable def finMax [Nonempty I] (a : I → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty a

theorem finMin_mem [Nonempty I] (a : I → ℝ) : ∃ i, a i = finMin a := by
  classical
  obtain ⟨i, _hi, hval⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty a
  exact ⟨i, hval.symm⟩

theorem finMax_mem [Nonempty I] (a : I → ℝ) : ∃ i, a i = finMax a := by
  classical
  obtain ⟨i, _hi, hval⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty a
  exact ⟨i, hval.symm⟩

/-- A finite probability vector, with nonnegativity and normalization bundled. -/
def ProbVec (I : Type u) [Fintype I] :=
  {p : I → ℝ // Nonneg p ∧ l1Mass p = 1}

/-- A finite sum in the nonnegative cone. -/
noncomputable def coneSum {J : Type v} [Fintype J] (z : J → ConeVec I) : ConeVec I :=
  ∑ j, z j

/-- A finite nonnegative weighted sum in the cone. -/
noncomputable def weightedConeSum {J : Type v} [Fintype J]
    (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (z : J → ConeVec I) : ConeVec I :=
  coneSum fun j => coneScale (c j) (hc j) (z j)

/-- A convex combination of probability vectors. -/
def mixProbVec (lambda : ℝ) (hlambda : lambda ∈ Icc (0 : ℝ) 1)
    (p q : ProbVec I) : ProbVec I :=
  ⟨fun i => lambda * p.1 i + (1 - lambda) * q.1 i,
    ⟨fun i => add_nonneg (mul_nonneg hlambda.1 (p.2.1 i))
        (mul_nonneg (sub_nonneg.mpr hlambda.2) (q.2.1 i)), by
      have hp : ∑ i, p.1 i = 1 := by simpa only [l1Mass] using p.2.2
      have hq : ∑ i, q.1 i = 1 := by simpa only [l1Mass] using q.2.2
      simp only [l1Mass, Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq]
      ring⟩⟩

/-- Concavity on the finite probability simplex. -/
def SimplexConcave (f : ProbVec I → ℝ) : Prop :=
  ∀ p q lambda (hlambda : lambda ∈ Icc (0 : ℝ) 1),
    lambda * f p + (1 - lambda) * f q ≤ f (mixProbVec lambda hlambda p q)

/-- Convexity on the finite probability simplex. -/
def SimplexConvex (f : ProbVec I → ℝ) : Prop :=
  ∀ p q lambda (hlambda : lambda ∈ Icc (0 : ℝ) 1),
    f (mixProbVec lambda hlambda p q) ≤ lambda * f p + (1 - lambda) * f q

/-- A binary probability vector with first coordinate `r`. -/
def binaryProb (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : ProbVec (Fin 2) :=
  ⟨fun i => if i = 0 then r else 1 - r,
    ⟨by
      intro i
      fin_cases i <;> simp [h0, sub_nonneg.mpr h1], by
      simp [l1Mass, Fin.sum_univ_two]⟩⟩

/-- A nonnegative finite vector has zero mass exactly when it is zero; a
nonzero such vector has strictly positive mass. -/
theorem nonzeroMass (x : I → ℝ) (hx : Nonneg x) :
    (l1Mass x = 0 ↔ x = 0) ∧ (x ≠ 0 ↔ 0 < l1Mass x) := by
  classical
  have hmass_nonneg : 0 ≤ l1Mass x := by
    exact Finset.sum_nonneg fun i _ => hx i
  have hzero : l1Mass x = 0 ↔ x = 0 := by
    constructor
    · intro hsum
      funext i
      have hle : x i ≤ l1Mass x := by
        exact Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      exact le_antisymm (by simpa [hsum] using hle) (hx i)
    · rintro rfl
      simp [l1Mass]
  refine ⟨hzero, ?_⟩
  constructor
  · intro hne
    exact lt_of_le_of_ne hmass_nonneg (fun h => hne (hzero.mp h.symm))
  · intro hpos hzeroFun
    subst x
    simp [l1Mass] at hpos

/-- A cone vector is nonzero exactly when its mass is positive. -/
theorem coneNonzeroMass (x : ConeVec I) :
    x ≠ 0 ↔ 0 < l1Mass x.1 := by
  have h := (nonzeroMass x.1 x.2).2
  constructor
  · intro hx
    apply h.mp
    intro hfun
    apply hx
    exact Subtype.ext hfun
  · intro hpos hx
    apply (h.mpr hpos)
    exact congrArg Subtype.val hx

/-- Normalize a nonzero cone vector to a probability vector. -/
noncomputable def normalize [Nonempty I] (x : PosConeVec I) : ProbVec I := by
  let m := l1Mass x.1.1
  have hm : 0 < m := (coneNonzeroMass x.1).mp (by
    intro hx0
    apply x.2
    exact congrArg Subtype.val hx0)
  exact ⟨fun i => x.1.1 i / m,
    ⟨fun i => div_nonneg (x.1.2 i) hm.le, by
      have hxsum : ∑ i, x.1.1 i = m := rfl
      change (∑ i, x.1.1 i * m⁻¹) = 1
      rw [← Finset.sum_mul, hxsum, mul_inv_cancel₀ hm.ne']⟩⟩

/-- Tensor product of finite probability vectors. -/
noncomputable def probTensor {J : Type v} [Fintype J]
    (p : ProbVec I) (q : ProbVec J) : ProbVec (I × J) :=
  ⟨fun z => p.1 z.1 * q.1 z.2,
    ⟨fun z => mul_nonneg (p.2.1 z.1) (q.2.1 z.2), by
      have hp : ∑ i, p.1 i = 1 := by simpa only [l1Mass] using p.2.2
      have hq : ∑ j, q.1 j = 1 := by simpa only [l1Mass] using q.2.2
      change (∑ z : I × J, p.1 z.1 * q.1 z.2) = 1
      rw [Fintype.sum_prod_type, ← Fintype.sum_mul_sum, hp, hq, one_mul]⟩⟩

/-- The uniform probability vector on a finite nonempty type. -/
noncomputable def uniformProb [Nonempty I] : ProbVec I :=
  ⟨fun _ => (Fintype.card I : ℝ)⁻¹,
    ⟨fun _ => inv_nonneg.mpr (Nat.cast_nonneg _), by
      simp only [l1Mass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [mul_inv_cancel₀]
      exact_mod_cast Fintype.card_ne_zero⟩⟩

/-- Raw zero extension along an injection. -/
noncomputable def zeroExtendRaw {J : Type v} [Fintype J]
    (e : I ↪ J) (x : I → ℝ) (j : J) : ℝ := by
  classical
  exact if h : j ∈ Set.range e then x (Classical.choose h) else 0

@[simp] theorem zeroExtendRaw_apply {J : Type v} [Fintype J]
    (e : I ↪ J) (x : I → ℝ) (i : I) :
    zeroExtendRaw e x (e i) = x i := by
  classical
  rw [zeroExtendRaw, dif_pos (show e i ∈ Set.range e from ⟨i, rfl⟩)]
  congr 1
  exact e.injective (Classical.choose_spec (show e i ∈ Set.range e from ⟨i, rfl⟩))

/-- Zero extension bundled in the nonnegative cone. -/
noncomputable def zeroExtendCone {J : Type v} [Fintype J]
    (e : I ↪ J) (x : ConeVec I) : ConeVec J :=
  ⟨zeroExtendRaw e x.1, by
    intro j
    classical
    rw [zeroExtendRaw]
    split <;> rename_i h
    · exact x.2 (Classical.choose h)
    · exact le_rfl⟩

/-- Zero extension bundled as a probability vector. -/
noncomputable def zeroExtendProb {J : Type v} [Fintype J]
    (e : I ↪ J) (p : ProbVec I) : ProbVec J := by
  classical
  refine ⟨zeroExtendRaw e p.1, ?_, ?_⟩
  · intro j
    rw [zeroExtendRaw]
    split <;> rename_i h
    · exact p.2.1 (Classical.choose h)
    · exact le_rfl
  · -- Reindex through the finite range of the embedding.
    have hp : ∑ i, p.1 i = 1 := by simpa only [l1Mass] using p.2.2
    rw [l1Mass]
    calc
      ∑ j : J, zeroExtendRaw e p.1 j =
          ∑ j ∈ Finset.univ.map e, zeroExtendRaw e p.1 j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        have hrange : j ∉ Set.range e := by
          rintro ⟨i, rfl⟩
          exact hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)
        rw [zeroExtendRaw, dif_neg hrange]
      _ = ∑ i : I, p.1 i := by simp
      _ = 1 := hp

@[simp] theorem l1Mass_prob (p : ProbVec I) : l1Mass p.1 = 1 :=
  p.2.2

@[simp] theorem l1Mass_coneScale (c : ℝ) (hc : 0 ≤ c) (x : ConeVec I) :
    l1Mass (coneScale c hc x).1 = c * l1Mass x.1 := by
  simp [l1Mass, coneScale, ← Finset.mul_sum]

@[simp] theorem normalize_apply [Nonempty I] (x : PosConeVec I) (i : I) :
    (normalize x).1 i = x.1.1 i / l1Mass x.1.1 := by
  rfl

/-- Positive scaling does not change the normalization of a cone vector. -/
theorem normalize_posScale [Nonempty I] (c : ℝ) (hc : 0 < c) (x : PosConeVec I) :
    normalize (posScale c hc x) = normalize x := by
  apply Subtype.ext
  funext i
  have hm : 0 < l1Mass x.1.1 := (coneNonzeroMass x.1).mp (by
    intro hx0
    apply x.2
    exact congrArg Subtype.val hx0)
  change c * x.1.1 i / l1Mass (fun j => c * x.1.1 j) =
    x.1.1 i / l1Mass x.1.1
  have hscale : l1Mass (fun j => c * x.1.1 j) = c * l1Mass x.1.1 := by
    simp [l1Mass, ← Finset.mul_sum]
  rw [hscale]
  field_simp [hc.ne', hm.ne']

/-- Reconstruction of a nonzero cone vector from its mass and normalization. -/
theorem normalize_reconstruct [Nonempty I] (x : PosConeVec I) (i : I) :
    x.1.1 i = l1Mass x.1.1 * (normalize x).1 i := by
  have hm : 0 < l1Mass x.1.1 := (coneNonzeroMass x.1).mp (by
    intro hx0
    apply x.2
    exact congrArg Subtype.val hx0)
  rw [normalize_apply]
  field_simp [hm.ne']

/-- A probability vector, viewed as a nonzero cone vector, normalizes to itself. -/
theorem normalize_prob [Nonempty I] (p : ProbVec I) :
    normalize (toPosCone (⟨p.1, p.2.1⟩ : ConeVec I) (by
      intro hp0
      have hfun : p.1 = 0 := congrArg Subtype.val hp0
      have hmass := p.2.2
      rw [hfun] at hmass
      simp [l1Mass] at hmass)) = p := by
  apply Subtype.ext
  funext i
  change p.1 i / l1Mass p.1 = p.1 i
  rw [p.2.2, div_one]

end Vectors

section Joint

variable {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]

/-- A finite joint probability matrix. -/
def JointProb (X : Type u) (Y : Type v) [Fintype X] [Fintype Y] :=
  {P : X → Y → ℝ //
    (∀ x y, 0 ≤ P x y) ∧ (∑ x, ∑ y, P x y) = 1}

/-- A column of a joint probability matrix, bundled in the cone. -/
def column (P : JointProb X Y) (y : Y) : ConeVec X :=
  ⟨fun x => P.1 x y, fun x => P.2.1 x y⟩

/-- The mass of one conditioning column. -/
noncomputable def colMass (P : JointProb X Y) (y : Y) : ℝ :=
  l1Mass (column P y).1

/-- Positive-mass conditioning outcomes. -/
noncomputable def activeFinset (P : JointProb X Y) : Finset Y :=
  Finset.univ.filter fun y => 0 < colMass P y

/-- The subtype of positive-mass conditioning outcomes. -/
abbrev Active (P : JointProb X Y) :=
  {y : Y // y ∈ activeFinset P}

/-- The canonical finite enumeration of the active-column subtype.  Keeping
this instance in the data layer ensures that every later candidate and
reindexing theorem uses the same enumeration definitionally. -/
noncomputable instance activeFintypeInstance (P : JointProb X Y) :
    Fintype (Active P) :=
  Fintype.ofFinset (activeFinset P) (fun _ ↦ Iff.rfl)

theorem active_colMass_pos (P : JointProb X Y) (y : Active P) :
    0 < colMass P y.1 := by
  have hy := y.2
  change y.1 ∈ Finset.univ.filter (fun z => 0 < colMass P z) at hy
  exact (Finset.mem_filter.mp hy).2

theorem active_column_ne_zero (P : JointProb X Y) (y : Active P) :
    column P y.1 ≠ 0 :=
  (coneNonzeroMass (column P y.1)).mpr (active_colMass_pos P y)

/-- The conditional probability vector of a positive-mass column. -/
noncomputable def conditional [Nonempty X]
    (P : JointProb X Y) (y : Active P) : ProbVec X :=
  normalize (toPosCone (column P y.1) (active_column_ne_zero P y))

@[simp] theorem conditional_apply [Nonempty X]
    (P : JointProb X Y) (y : Active P) (x : X) :
    (conditional P y).1 x = P.1 x y.1 / colMass P y.1 := by
  rfl

/-- Reconstruct an active joint column from its mass and conditional law. -/
theorem active_column_reconstruct [Nonempty X]
    (P : JointProb X Y) (y : Active P) (x : X) :
    P.1 x y.1 = colMass P y.1 * (conditional P y).1 x := by
  exact normalize_reconstruct
    (toPosCone (column P y.1) (active_column_ne_zero P y)) x

/-- Independent product joint distribution. -/
noncomputable def independentJoint (p : ProbVec X) (q : ProbVec Y) : JointProb X Y :=
  ⟨fun x y => p.1 x * q.1 y,
    ⟨fun x y => mul_nonneg (p.2.1 x) (q.2.1 y), by
      have hp : ∑ x, p.1 x = 1 := by simpa only [l1Mass] using p.2.2
      have hq : ∑ y, q.1 y = 1 := by simpa only [l1Mass] using q.2.2
      change (∑ x, ∑ y, p.1 x * q.1 y) = 1
      rw [← Fintype.sum_mul_sum, hp, hq, one_mul]⟩⟩

theorem independentColumnMass (p : ProbVec X) (q : ProbVec Y) (y : Y) :
    colMass (independentJoint p q) y = q.1 y := by
  have hp : ∑ x, p.1 x = 1 := by simpa only [l1Mass] using p.2.2
  change (∑ x, p.1 x * q.1 y) = q.1 y
  rw [← Finset.sum_mul, hp, one_mul]

/-- An active outcome in an independent joint distribution. -/
noncomputable def independentActive (p : ProbVec X) (q : ProbVec Y)
    (y : Y) (hy : 0 < q.1 y) : Active (independentJoint p q) :=
  ⟨y, by simpa [activeFinset, independentColumnMass] using hy⟩

@[simp] theorem independentConditional [Nonempty X]
    (p : ProbVec X) (q : ProbVec Y) (y : Y) (hy : 0 < q.1 y) :
    conditional (independentJoint p q) (independentActive p q y hy) = p := by
  apply Subtype.ext
  funext x
  rw [conditional_apply, independentColumnMass]
  change p.1 x * q.1 y / q.1 y = p.1 x
  field_simp [hy.ne']

/-- Tensor product of joint probability matrices. -/
noncomputable def jointTensor {X' : Type u'} {Y' : Type v'}
    [Fintype X'] [Fintype Y']
    (P : JointProb X Y) (Q : JointProb X' Y') : JointProb (X × X') (Y × Y') :=
  ⟨fun xx yy => P.1 xx.1 yy.1 * Q.1 xx.2 yy.2,
    ⟨fun xx yy => mul_nonneg (P.2.1 xx.1 yy.1) (Q.2.1 xx.2 yy.2), by
      let shuffle : ((X × X') × (Y × Y')) ≃ ((X × Y) × (X' × Y')) :=
        { toFun := fun z => ((z.1.1, z.2.1), (z.1.2, z.2.2))
          invFun := fun z => ((z.1.1, z.2.1), (z.1.2, z.2.2))
          left_inv := by intro z; rfl
          right_inv := by intro z; rfl }
      have hP : ∑ x, ∑ y, P.1 x y = 1 := P.2.2
      have hQ : ∑ x, ∑ y, Q.1 x y = 1 := Q.2.2
      calc
        ∑ (xx : X × X'), ∑ (yy : Y × Y'),
            P.1 xx.1 yy.1 * Q.1 xx.2 yy.2 =
            ∑ z : ((X × X') × (Y × Y')),
              P.1 z.1.1 z.2.1 * Q.1 z.1.2 z.2.2 := by
                simpa only using (Fintype.sum_prod_type
                  (fun z : (X × X') × (Y × Y') =>
                    P.1 z.1.1 z.2.1 * Q.1 z.1.2 z.2.2)).symm
        _ = ∑ z : ((X × Y) × (X' × Y')),
              P.1 z.1.1 z.1.2 * Q.1 z.2.1 z.2.2 := by
                exact Fintype.sum_equiv shuffle _ _ (fun _ => rfl)
        _ = (∑ z : X × Y, P.1 z.1 z.2) *
              ∑ z : X' × Y', Q.1 z.1 z.2 := by
                rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]
        _ = 1 := by
          simp only [Fintype.sum_prod_type, hP, hQ, one_mul]⟩⟩

/-- Positive conditioning columns are nonempty and their masses sum to one. -/
theorem positiveColumnsNonempty (P : JointProb X Y) :
    (activeFinset P).Nonempty ∧ ∑ y ∈ activeFinset P, colMass P y = 1 := by
  classical
  have hmass_nonneg : ∀ y, 0 ≤ colMass P y := fun y =>
    Finset.sum_nonneg fun x _ => P.2.1 x y
  have htotal : ∑ y, colMass P y = 1 := by
    simp only [colMass, column, l1Mass]
    rw [Finset.sum_comm]
    exact P.2.2
  have hfilter : ∑ y ∈ activeFinset P, colMass P y = ∑ y, colMass P y := by
    rw [activeFinset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs with hy
    · rfl
    · have hz : colMass P y = 0 := le_antisymm (not_lt.mp hy) (hmass_nonneg y)
      exact hz.symm
  refine ⟨?_, hfilter.trans htotal⟩
  by_contra hempty
  have : ∑ y ∈ activeFinset P, colMass P y = 0 := by
    simp [Finset.not_nonempty_iff_eq_empty.mp hempty]
  linarith [hfilter.trans htotal]

/-- A local nonempty witness for the active-outcome subtype. -/
theorem activeNonempty (P : JointProb X Y) : Nonempty (Active P) :=
  let y := (positiveColumnsNonempty P).1.choose
  ⟨⟨y, (positiveColumnsNonempty P).1.choose_spec⟩⟩

/-- Every joint probability law has at least one positive-mass column. -/
noncomputable instance activeNonemptyInstance (P : JointProb X Y) :
    Nonempty (Active P) :=
  activeNonempty P

end Joint

end ConditionalEntropy
