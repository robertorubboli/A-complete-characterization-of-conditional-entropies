import ConditionalEntropy.Basic

/-!
# Finite midpoint counterexamples

These lemmas are the order-theoretic endpoint of Appendix B.5--B.6.  Once a
strict second-order sign has produced two finite endpoints, the corresponding
shape property is contradicted directly.
-/

namespace ConditionalEntropy

theorem not_concave_of_strict_midpoint_valley
    {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : E → ℝ) (x z : E)
    (hmid : f ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • z) <
      (1 / 2 : ℝ) * f x + (1 / 2 : ℝ) * f z) :
    ¬ IsConcave f := by
  intro hconc
  have h := hconc x z (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hone : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
  rw [hone] at h
  exact (not_lt_of_ge h) hmid

theorem not_convex_of_strict_midpoint_peak
    {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : E → ℝ) (x z : E)
    (hmid : (1 / 2 : ℝ) * f x + (1 / 2 : ℝ) * f z <
      f ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • z)) :
    ¬ IsConvex f := by
  intro hconv
  have h := hconv x z (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hone : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
  rw [hone] at h
  exact (not_lt_of_ge h) hmid

theorem not_quasiConvex_of_strict_midpoint_peak
    {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : E → ℝ) (x z : E)
    (hmid : max (f x) (f z) < f ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • z)) :
    ¬ IsQuasiConvex f := by
  intro hquasi
  have h := hquasi x z (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hone : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
  rw [hone] at h
  exact (not_lt_of_ge h) hmid

end ConditionalEntropy
