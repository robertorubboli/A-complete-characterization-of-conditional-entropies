import ConditionalEntropy.FiniteData

/-!
# Algebra of finite extrema

The tropical candidates use total minima and maxima on finite nonempty
types.  This file records their Lipschitz and product-additivity laws.
-/

noncomputable section

open scoped BigOperators

namespace ConditionalEntropy

universe u v

theorem finMin_le {I : Type u} [Fintype I] [Nonempty I]
    (a : I → ℝ) (i : I) : finMin a ≤ a i := by
  unfold finMin
  exact Finset.inf'_le _ (Finset.mem_univ i)

theorem le_finMax_apply {I : Type u} [Fintype I] [Nonempty I]
    (a : I → ℝ) (i : I) : a i ≤ finMax a := by
  unfold finMax
  exact Finset.le_sup' a (Finset.mem_univ i)

theorem finMin_mono {I : Type u} [Fintype I] [Nonempty I]
    {a b : I → ℝ} (h : ∀ i, a i ≤ b i) : finMin a ≤ finMin b := by
  obtain ⟨i, hi⟩ := finMin_mem b
  calc
    finMin a ≤ a i := finMin_le a i
    _ ≤ b i := h i
    _ = finMin b := hi

theorem finMax_mono {I : Type u} [Fintype I] [Nonempty I]
    {a b : I → ℝ} (h : ∀ i, a i ≤ b i) : finMax a ≤ finMax b := by
  obtain ⟨i, hi⟩ := finMax_mem a
  calc
    finMax a = a i := hi.symm
    _ ≤ b i := h i
    _ ≤ finMax b := le_finMax_apply b i

/-- Finite minimum is one-Lipschitz for the sup norm. -/
theorem abs_finMin_sub_le {I : Type u} [Fintype I] [Nonempty I]
    (a b : I → ℝ) :
    |finMin a - finMin b| ≤ finMax (fun i => |a i - b i|) := by
  rw [abs_le]
  constructor
  · obtain ⟨i, hi⟩ := finMin_mem a
    have habs := le_finMax_apply (fun j => |a j - b j|) i
    have hpoint : b i - a i ≤ |a i - b i| := by
      simpa [abs_sub_comm] using le_abs_self (b i - a i)
    calc
      -(finMax (fun i => |a i - b i|)) ≤ -|a i - b i| := neg_le_neg habs
      _ ≤ a i - b i := by linarith [hpoint]
      _ ≤ finMin a - finMin b := by
        rw [hi]
        linarith [finMin_le b i]
  · obtain ⟨i, hi⟩ := finMin_mem b
    have habs := le_finMax_apply (fun j => |a j - b j|) i
    calc
      finMin a - finMin b ≤ a i - b i := by
        rw [hi]
        linarith [finMin_le a i]
      _ ≤ |a i - b i| := le_abs_self _
      _ ≤ finMax (fun j => |a j - b j|) := habs

/-- Finite maximum is one-Lipschitz for the sup norm. -/
theorem abs_finMax_sub_le {I : Type u} [Fintype I] [Nonempty I]
    (a b : I → ℝ) :
    |finMax a - finMax b| ≤ finMax (fun i => |a i - b i|) := by
  rw [abs_le]
  constructor
  · obtain ⟨i, hi⟩ := finMax_mem b
    have habs := le_finMax_apply (fun j => |a j - b j|) i
    calc
      -(finMax (fun i => |a i - b i|)) ≤ -|a i - b i| := neg_le_neg habs
      _ ≤ a i - b i := by
        have hpoint : b i - a i ≤ |a i - b i| := by
          simpa [abs_sub_comm] using le_abs_self (b i - a i)
        linarith
      _ ≤ finMax a - finMax b := by
        rw [hi]
        linarith [le_finMax_apply a i]
  · obtain ⟨i, hi⟩ := finMax_mem a
    have habs := le_finMax_apply (fun j => |a j - b j|) i
    calc
      finMax a - finMax b ≤ a i - b i := by
        rw [hi]
        linarith [le_finMax_apply b i]
      _ ≤ |a i - b i| := le_abs_self _
      _ ≤ finMax (fun j => |a j - b j|) := habs

/-- A separated sum has minimum equal to the sum of the two minima. -/
theorem finMin_prod_add {I : Type u} {J : Type v}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (a : I → ℝ) (b : J → ℝ) :
    finMin (fun ij : I × J => a ij.1 + b ij.2) = finMin a + finMin b := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := finMin_mem a
    obtain ⟨j, hj⟩ := finMin_mem b
    calc
      finMin (fun ij : I × J => a ij.1 + b ij.2) ≤ a i + b j :=
        finMin_le _ (i, j)
      _ = finMin a + finMin b := by rw [hi, hj]
  · obtain ⟨ij, hij⟩ := finMin_mem
        (fun ij : I × J => a ij.1 + b ij.2)
    calc
      finMin a + finMin b ≤ a ij.1 + b ij.2 :=
        add_le_add (finMin_le a ij.1) (finMin_le b ij.2)
      _ = finMin (fun ij : I × J => a ij.1 + b ij.2) := hij

/-- A separated sum has maximum equal to the sum of the two maxima. -/
theorem finMax_prod_add {I : Type u} {J : Type v}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (a : I → ℝ) (b : J → ℝ) :
    finMax (fun ij : I × J => a ij.1 + b ij.2) = finMax a + finMax b := by
  apply le_antisymm
  · obtain ⟨ij, hij⟩ := finMax_mem
        (fun ij : I × J => a ij.1 + b ij.2)
    calc
      finMax (fun ij : I × J => a ij.1 + b ij.2) = a ij.1 + b ij.2 := hij.symm
      _ ≤ finMax a + finMax b :=
        add_le_add (le_finMax_apply a ij.1) (le_finMax_apply b ij.2)
  · obtain ⟨i, hi⟩ := finMax_mem a
    obtain ⟨j, hj⟩ := finMax_mem b
    calc
      finMax a + finMax b = a i + b j := by rw [hi, hj]
      _ ≤ finMax (fun ij : I × J => a ij.1 + b ij.2) :=
        le_finMax_apply (fun ij : I × J => a ij.1 + b ij.2) (i, j)

/-- The exact four-way finite-extrema package from the blueprint. -/
theorem finiteExtrema {I : Type u} {J : Type v}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (a b c : I → ℝ) (d : J → ℝ) :
    |finMin a - finMin b| ≤ finMax (fun i => |a i - b i|) ∧
    |finMax a - finMax b| ≤ finMax (fun i => |a i - b i|) ∧
    finMin (fun ij : I × J => c ij.1 + d ij.2) = finMin c + finMin d ∧
    finMax (fun ij : I × J => c ij.1 + d ij.2) = finMax c + finMax d :=
  ⟨abs_finMin_sub_le a b, abs_finMax_sub_le a b,
    finMin_prod_add c d, finMax_prod_add c d⟩

end ConditionalEntropy
