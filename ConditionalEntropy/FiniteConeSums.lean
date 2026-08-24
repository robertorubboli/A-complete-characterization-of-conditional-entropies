import ConditionalEntropy.ColumnFunctions

/-!
# Homogeneous curvature and finite cone sums

Degree-one concavity is superadditive and degree-one convexity is
subadditive.  The finite weighted forms are the algebraic engine of the
conditional-channel shape reductions.
-/

noncomputable section

open scoped BigOperators

namespace ConditionalEntropy

universe u v

theorem posHomOne_zero {I : Type u} (F : ConeVec I → ℝ)
    (hF : PosHomOne F) : F 0 = 0 := by
  have h := hF 0 0 (le_refl 0)
  have hscale : coneScale 0 (le_refl 0) (0 : ConeVec I) = 0 := by
    apply Subtype.ext
    funext i
    simp [coneScale]
  rw [hscale] at h
  simpa using h

theorem concaveCone_superadditive {I : Type u}
    (F : ConeVec I → ℝ) (hF : PosHomOne F) (hconc : ConcaveCone F)
    (x z : ConeVec I) : F x + F z ≤ F (x + z) := by
  let hhalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  let m := coneMix (1 / 2 : ℝ) hhalf x z
  have hmid := hconc x z (1 / 2 : ℝ) hhalf
  have hscale := hF m 2 (by norm_num)
  have heq : coneScale 2 (by norm_num) m = x + z := by
    apply Subtype.ext
    funext i
    simp [m, coneScale, coneMix]
    ring
  calc
    F x + F z = 2 * ((1 / 2 : ℝ) * F x + (1 - 1 / 2) * F z) := by ring
    _ ≤ 2 * F m := mul_le_mul_of_nonneg_left hmid (by norm_num)
    _ = F (x + z) := by rw [← hscale, heq]

theorem convexCone_subadditive {I : Type u}
    (F : ConeVec I → ℝ) (hF : PosHomOne F) (hconv : ConvexCone F)
    (x z : ConeVec I) : F (x + z) ≤ F x + F z := by
  let hhalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  let m := coneMix (1 / 2 : ℝ) hhalf x z
  have hmid := hconv x z (1 / 2 : ℝ) hhalf
  have hscale := hF m 2 (by norm_num)
  have heq : coneScale 2 (by norm_num) m = x + z := by
    apply Subtype.ext
    funext i
    simp [m, coneScale, coneMix]
    ring
  calc
    F (x + z) = 2 * F m := by rw [← heq, hscale]
    _ ≤ 2 * ((1 / 2 : ℝ) * F x + (1 - 1 / 2) * F z) :=
      mul_le_mul_of_nonneg_left hmid (by norm_num)
    _ = F x + F z := by ring

theorem concaveCone_sum_le {I : Type u} {J : Type v}
    [Fintype J] (F : ConeVec I → ℝ) (hF : PosHomOne F)
    (hconc : ConcaveCone F) (z : J → ConeVec I) :
    (∑ j, F (z j)) ≤ F (coneSum z) := by
  classical
  have hzero : F 0 = 0 := posHomOne_zero F hF
  have aux : ∀ s : Finset J,
      (∑ j ∈ s, F (z j)) ≤ F (∑ j ∈ s, z j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | @insert a s ha ih =>
        calc
          (∑ j ∈ insert a s, F (z j)) = F (z a) + ∑ j ∈ s, F (z j) := by
            simp [ha]
          _ ≤ F (z a) + F (∑ j ∈ s, z j) := add_le_add (le_refl _) ih
          _ ≤ F (z a + ∑ j ∈ s, z j) :=
            concaveCone_superadditive F hF hconc _ _
          _ = F (∑ j ∈ insert a s, z j) := by simp [ha]
  simpa [coneSum] using aux Finset.univ

theorem convexCone_sum_le {I : Type u} {J : Type v}
    [Fintype J] (F : ConeVec I → ℝ) (hF : PosHomOne F)
    (hconv : ConvexCone F) (z : J → ConeVec I) :
    F (coneSum z) ≤ ∑ j, F (z j) := by
  classical
  have hzero : F 0 = 0 := posHomOne_zero F hF
  have aux : ∀ s : Finset J,
      F (∑ j ∈ s, z j) ≤ ∑ j ∈ s, F (z j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | @insert a s ha ih =>
        calc
          F (∑ j ∈ insert a s, z j) = F (z a + ∑ j ∈ s, z j) := by
            simp [ha]
          _ ≤ F (z a) + F (∑ j ∈ s, z j) :=
            convexCone_subadditive F hF hconv _ _
          _ ≤ F (z a) + ∑ j ∈ s, F (z j) := add_le_add (le_refl _) ih
          _ = ∑ j ∈ insert a s, F (z j) := by simp [ha]
  simpa [coneSum] using aux Finset.univ

/-- Exact four-way finite homogeneous-sum package. -/
theorem homogeneousFiniteSums {I : Type u} {J : Type v}
    [Nonempty I] [Fintype J]
    (F : ConeVec I → ℝ) (hF : PosHomOne F)
    (z : J → ConeVec I) (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) :
    (ConcaveCone F → (∑ j, F (z j)) ≤ F (coneSum z)) ∧
    (ConvexCone F ∧ F 0 = 0 → F (coneSum z) ≤ ∑ j, F (z j)) ∧
    (ConcaveCone F →
      (∑ j, c j * F (z j)) ≤ F (weightedConeSum c hc z)) ∧
    (ConvexCone F ∧ F 0 = 0 →
      F (weightedConeSum c hc z) ≤ ∑ j, c j * F (z j)) := by
  constructor
  · exact fun hconc => concaveCone_sum_le F hF hconc z
  constructor
  · exact fun hconv => convexCone_sum_le F hF hconv.1 z
  constructor
  · intro hconc
    calc
      (∑ j, c j * F (z j)) =
          ∑ j, F (coneScale (c j) (hc j) (z j)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact (hF (z j) (c j) (hc j)).symm
      _ ≤ F (coneSum fun j => coneScale (c j) (hc j) (z j)) :=
        concaveCone_sum_le F hF hconc _
      _ = F (weightedConeSum c hc z) := rfl
  · intro hconv
    calc
      F (weightedConeSum c hc z) =
          F (coneSum fun j => coneScale (c j) (hc j) (z j)) := rfl
      _ ≤ ∑ j, F (coneScale (c j) (hc j) (z j)) :=
        convexCone_sum_le F hF hconv.1 _
      _ = ∑ j, c j * F (z j) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hF (z j) (c j) (hc j)

end ConditionalEntropy
