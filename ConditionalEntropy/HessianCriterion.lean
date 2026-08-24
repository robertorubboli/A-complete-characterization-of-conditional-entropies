import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv

/-!
# Hessian sign criterion on a finite-dimensional real space

This module records the literal generic Hessian declarations used in
Section 4 of the manuscript.  The sign criterion is proved by restricting
the function to each affine line segment and applying the one-dimensional
second-derivative criterion.
-/

noncomputable section

open Set

namespace ConditionalEntropy

/-- The quadratic form obtained by evaluating the second Frechet derivative
twice in the same direction. -/
def hessianQuad (F : (Fin n → ℝ) → ℝ)
    (x v : Fin n → ℝ) : ℝ :=
  (fderiv ℝ (fun y ↦ fderiv ℝ F y) x v) v

private theorem concaveOn_of_hessianQuad_nonpos
    {U : Set (Fin n → ℝ)} (hUopen : IsOpen U) (hUconv : Convex ℝ U)
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiffOn ℝ 2 F U)
    (hquad : ∀ x ∈ U, ∀ v : Fin n → ℝ, hessianQuad F x v ≤ 0) :
    ConcaveOn ℝ U F := by
  have hFdiff : DifferentiableOn ℝ F U :=
    hF.differentiableOn (by norm_num)
  have hDf : ContDiffOn ℝ 1 (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hUopen (by norm_num)
  have hDfdiff : DifferentiableOn ℝ (fderiv ℝ F) U :=
    hDf.differentiableOn_one
  refine ⟨hUconv, ?_⟩
  intro x hx y hy a b ha hb hab
  let line : ℝ → (Fin n → ℝ) := AffineMap.lineMap x y
  let v : Fin n → ℝ := y - x
  let g : ℝ → ℝ := F ∘ line
  let g' : ℝ → ℝ := fun t ↦ fderiv ℝ F (line t) v
  let g'' : ℝ → ℝ := fun t ↦ hessianQuad F (line t) v
  have hline_mem : MapsTo line (Icc (0 : ℝ) 1) U := by
    intro t ht
    exact hUconv.lineMap_mem hx hy ht
  have hg_cont : ContinuousOn g (Icc (0 : ℝ) 1) := by
    exact hF.continuousOn.comp AffineMap.lineMap_continuous.continuousOn
      hline_mem
  have hg_first : ∀ t ∈ interior (Icc (0 : ℝ) 1),
      HasDerivWithinAt g (g' t) (interior (Icc (0 : ℝ) 1)) t := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
    have hlt : line t ∈ U := hline_mem htIcc
    have hFAt : HasFDerivAt F (fderiv ℝ F (line t)) (line t) :=
      ((hFdiff (line t) hlt).differentiableAt
        (hUopen.mem_nhds hlt)).hasFDerivAt
    have hlineAt : HasDerivAt line v t := by
      simpa only [line, v] using
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))
    exact (hFAt.comp_hasDerivAt t hlineAt).hasDerivWithinAt
  have hg_second : ∀ t ∈ interior (Icc (0 : ℝ) 1),
      HasDerivWithinAt g' (g'' t) (interior (Icc (0 : ℝ) 1)) t := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
    have hlt : line t ∈ U := hline_mem htIcc
    have hDfAt : HasFDerivAt (fderiv ℝ F)
        (fderiv ℝ (fun z ↦ fderiv ℝ F z) (line t)) (line t) :=
      ((hDfdiff (line t) hlt).differentiableAt
        (hUopen.mem_nhds hlt)).hasFDerivAt
    have hlineAt : HasDerivAt line v t := by
      simpa only [line, v] using
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))
    have hc : HasDerivAt ((fderiv ℝ F) ∘ line)
        ((fderiv ℝ (fun z ↦ fderiv ℝ F z) (line t)) v) t :=
      hDfAt.comp_hasDerivAt t hlineAt
    have hv : HasDerivAt (fun _ : ℝ ↦ v) 0 t := hasDerivAt_const t v
    have happ := hc.clm_apply hv
    simpa only [g', g'', Function.comp_apply, hessianQuad,
      ContinuousLinearMap.map_zero, add_zero] using happ.hasDerivWithinAt
  have hg_quad : ∀ t ∈ interior (Icc (0 : ℝ) 1), g'' t ≤ 0 := by
    intro t ht
    exact hquad (line t) (hline_mem (interior_subset ht)) v
  have hg_conc : ConcaveOn ℝ (Icc (0 : ℝ) 1) g :=
    concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
      hg_cont hg_first hg_second hg_quad
  have hineq := hg_conc.2 (x := (0 : ℝ)) (by simp)
    (y := (1 : ℝ)) (by simp) ha hb hab
  have hab' : 1 - b = a := by linarith
  simpa only [g, line, Function.comp_apply, AffineMap.lineMap_apply_module,
    smul_eq_mul, mul_zero, mul_one, zero_smul, one_smul, sub_zero,
    sub_self, add_zero, zero_add, hab'] using hineq

private theorem convexOn_of_hessianQuad_nonneg
    {U : Set (Fin n → ℝ)} (hUopen : IsOpen U) (hUconv : Convex ℝ U)
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiffOn ℝ 2 F U)
    (hquad : ∀ x ∈ U, ∀ v : Fin n → ℝ, 0 ≤ hessianQuad F x v) :
    ConvexOn ℝ U F := by
  have hFdiff : DifferentiableOn ℝ F U :=
    hF.differentiableOn (by norm_num)
  have hDf : ContDiffOn ℝ 1 (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hUopen (by norm_num)
  have hDfdiff : DifferentiableOn ℝ (fderiv ℝ F) U :=
    hDf.differentiableOn_one
  refine ⟨hUconv, ?_⟩
  intro x hx y hy a b ha hb hab
  let line : ℝ → (Fin n → ℝ) := AffineMap.lineMap x y
  let v : Fin n → ℝ := y - x
  let g : ℝ → ℝ := F ∘ line
  let g' : ℝ → ℝ := fun t ↦ fderiv ℝ F (line t) v
  let g'' : ℝ → ℝ := fun t ↦ hessianQuad F (line t) v
  have hline_mem : MapsTo line (Icc (0 : ℝ) 1) U := by
    intro t ht
    exact hUconv.lineMap_mem hx hy ht
  have hg_cont : ContinuousOn g (Icc (0 : ℝ) 1) := by
    exact hF.continuousOn.comp AffineMap.lineMap_continuous.continuousOn
      hline_mem
  have hg_first : ∀ t ∈ interior (Icc (0 : ℝ) 1),
      HasDerivWithinAt g (g' t) (interior (Icc (0 : ℝ) 1)) t := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
    have hlt : line t ∈ U := hline_mem htIcc
    have hFAt : HasFDerivAt F (fderiv ℝ F (line t)) (line t) :=
      ((hFdiff (line t) hlt).differentiableAt
        (hUopen.mem_nhds hlt)).hasFDerivAt
    have hlineAt : HasDerivAt line v t := by
      simpa only [line, v] using
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))
    exact (hFAt.comp_hasDerivAt t hlineAt).hasDerivWithinAt
  have hg_second : ∀ t ∈ interior (Icc (0 : ℝ) 1),
      HasDerivWithinAt g' (g'' t) (interior (Icc (0 : ℝ) 1)) t := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
    have hlt : line t ∈ U := hline_mem htIcc
    have hDfAt : HasFDerivAt (fderiv ℝ F)
        (fderiv ℝ (fun z ↦ fderiv ℝ F z) (line t)) (line t) :=
      ((hDfdiff (line t) hlt).differentiableAt
        (hUopen.mem_nhds hlt)).hasFDerivAt
    have hlineAt : HasDerivAt line v t := by
      simpa only [line, v] using
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))
    have hc : HasDerivAt ((fderiv ℝ F) ∘ line)
        ((fderiv ℝ (fun z ↦ fderiv ℝ F z) (line t)) v) t :=
      hDfAt.comp_hasDerivAt t hlineAt
    have hv : HasDerivAt (fun _ : ℝ ↦ v) 0 t := hasDerivAt_const t v
    have happ := hc.clm_apply hv
    simpa only [g', g'', Function.comp_apply, hessianQuad,
      ContinuousLinearMap.map_zero, add_zero] using happ.hasDerivWithinAt
  have hg_quad : ∀ t ∈ interior (Icc (0 : ℝ) 1), 0 ≤ g'' t := by
    intro t ht
    exact hquad (line t) (hline_mem (interior_subset ht)) v
  have hg_conv : ConvexOn ℝ (Icc (0 : ℝ) 1) g :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
      hg_cont hg_first hg_second hg_quad
  have hineq := hg_conv.2 (x := (0 : ℝ)) (by simp)
    (y := (1 : ℝ)) (by simp) ha hb hab
  have hab' : 1 - b = a := by linarith
  simpa only [g, line, Function.comp_apply, AffineMap.lineMap_apply_module,
    smul_eq_mul, mul_zero, mul_one, zero_smul, one_smul, sub_zero,
    sub_self, add_zero, zero_add, hab'] using hineq

/-- On an open convex subset of a finite-dimensional real space, a
nonpositive Hessian quadratic form implies concavity, while a nonnegative
Hessian quadratic form implies convexity. -/
theorem hessianSignCriterion (n : ℕ) (U : Set (Fin n → ℝ))
    (hUopen : IsOpen U) (hUconv : Convex ℝ U)
    (F : (Fin n → ℝ) → ℝ) (hF : ContDiffOn ℝ 2 F U) :
    ((∀ x ∈ U, ∀ v : Fin n → ℝ, hessianQuad F x v ≤ 0) →
      ConcaveOn ℝ U F) ∧
    ((∀ x ∈ U, ∀ v : Fin n → ℝ, 0 ≤ hessianQuad F x v) →
      ConvexOn ℝ U F) := by
  exact ⟨concaveOn_of_hessianQuad_nonpos hUopen hUconv hF,
    convexOn_of_hessianQuad_nonneg hUopen hUconv hF⟩

end ConditionalEntropy
