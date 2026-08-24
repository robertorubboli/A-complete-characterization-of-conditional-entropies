import BoundaryProofs.Curvature
import ConditionalEntropy.CurvatureObstructions
import ConditionalEntropy.LineCalculus
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.MeanInequalities

/-!
# Affine monomials on the positive orthant

This module supplies the finite-dimensional monomial calculus used in the
finite-support factorisation.  The exponent family is affine (its sum is
one), but individual exponents may have either sign.
-/

noncomputable section

open Set
open Filter
open scoped BigOperators Topology

namespace ConditionalEntropy

universe u

variable {ι : Type u} [Fintype ι]

/-- The open positive orthant in a finite real coordinate space. -/
def positiveOrthant : Set (ι → ℝ) :=
  {y | ∀ i, 0 < y i}

/-- The affine monomial with exponent vector `β`. -/
def affineMonomial (β : ι → ℝ) (y : ι → ℝ) : ℝ :=
  ∏ i, y i ^ β i

omit [Fintype ι] in
theorem positiveOrthant_convex : Convex ℝ (positiveOrthant : Set (ι → ℝ)) := by
  intro x hx y hy a b ha hb hab i
  rcases ha.eq_or_lt with rfl | hapos
  · have hb_one : b = 1 := by linarith
    simpa [hb_one] using hy i
  · exact add_pos_of_pos_of_nonneg (mul_pos hapos (hx i))
      (mul_nonneg hb (hy i).le)

omit [Fintype ι] in
theorem positiveOrthant_isOpen [Finite ι] :
    IsOpen (positiveOrthant : Set (ι → ℝ)) := by
  have hfinite : (Set.univ : Set ι).Finite := Set.toFinite _
  have hopen : IsOpen ((Set.univ : Set ι).pi (fun _ => Ioi (0 : ℝ))) :=
    isOpen_set_pi hfinite (fun _ _ => isOpen_Ioi)
  have heq : (positiveOrthant : Set (ι → ℝ)) =
      (Set.univ : Set ι).pi (fun _ => Ioi (0 : ℝ)) := by
    ext y
    simp only [positiveOrthant, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
      Set.mem_Ioi, forall_const]
  rw [heq]
  exact hopen

theorem affineMonomial_pos (β : ι → ℝ) {y : ι → ℝ}
    (hy : y ∈ (positiveOrthant : Set (ι → ℝ))) :
    0 < affineMonomial β y := by
  unfold affineMonomial
  exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hy i) _

/-- Translating all logarithmic velocities by a common constant leaves the
affine monomial curvature unchanged. -/
theorem monomialCurvature_add_const (β a : ι → ℝ) (c : ℝ)
    (hsum : IsAffineFamily β) :
    monomialCurvature β (fun i => a i + c) = monomialCurvature β a := by
  have hsum' : ∑ i, β i = 1 := hsum
  have hlinear :
      (∑ i, β i * (a i + c)) = (∑ i, β i * a i) + c := by
    calc
      (∑ i, β i * (a i + c)) =
          (∑ i, β i * a i) + ∑ i, β i * c := by
        simp_rw [mul_add]
        exact Finset.sum_add_distrib
      _ = (∑ i, β i * a i) + (∑ i, β i) * c := by
        rw [Finset.sum_mul]
      _ = (∑ i, β i * a i) + c := by rw [hsum']; ring
  have hquadratic :
      (∑ i, β i * (a i + c) ^ 2) =
        (∑ i, β i * a i ^ 2) + 2 * c * (∑ i, β i * a i) + c ^ 2 := by
    calc
      (∑ i, β i * (a i + c) ^ 2) =
          ∑ i, (β i * a i ^ 2 + 2 * c * (β i * a i) + c ^ 2 * β i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, β i * a i ^ 2) +
          2 * c * (∑ i, β i * a i) + c ^ 2 * (∑ i, β i) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp only [Finset.mul_sum]
      _ = (∑ i, β i * a i ^ 2) + 2 * c * (∑ i, β i * a i) + c ^ 2 := by
        rw [hsum']
        ring
  unfold monomialCurvature
  rw [hlinear, hquadratic]
  ring

/-- If one exponent is positive and every other exponent is nonpositive, the
affine monomial Hessian quadratic form is nonnegative. -/
theorem monomialCurvature_nonneg_of_uniquePositive (β a : ι → ℝ)
    (hsum : IsAffineFamily β) (hunique : HasUniquePositive β) :
    0 ≤ monomialCurvature β a := by
  classical
  obtain ⟨k, _hkpos, hk⟩ := hunique
  let d : ι → ℝ := fun i => a i - a k
  have hd_k : d k = 0 := by simp [d]
  have hquad : ∑ i, β i * d i ^ 2 ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    by_cases hik : i = k
    · subst i
      simp [hd_k]
    · exact mul_nonpos_of_nonpos_of_nonneg (hk i hik) (sq_nonneg _)
  have hcurvD : 0 ≤ monomialCurvature β d := by
    unfold monomialCurvature
    nlinarith [sq_nonneg (∑ i, β i * d i)]
  have ha_eq : (fun i => d i + a k) = a := by
    funext i
    simp [d]
  rw [← ha_eq, monomialCurvature_add_const β d (a k) hsum]
  exact hcurvD

/-- Changing a single positive coordinate in the monotonicity direction of
its exponent changes the affine monomial in the same direction. -/
theorem affineMonomial_coord_mono (β : ι → ℝ) (j : ι) (hβ : 0 ≤ β j)
    {a b : ι → ℝ} (ha : a ∈ (positiveOrthant : Set (ι → ℝ)))
    (hb : b ∈ (positiveOrthant : Set (ι → ℝ)))
    (hab : ∀ i, i ≠ j → a i = b i) (haj : a j ≤ b j) :
    affineMonomial β a ≤ affineMonomial β b := by
  classical
  have hpow : a j ^ β j ≤ b j ^ β j :=
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hβ)
      (le_of_lt (ha j)) (le_of_lt (hb j)) haj
  let R : ℝ := ∏ i ∈ Finset.univ.erase j, a i ^ β i
  have hRpos : 0 < R := by
    apply Finset.prod_pos
    intro i hi
    exact Real.rpow_pos_of_pos (ha i) _
  have hrest : (∏ i ∈ Finset.univ.erase j, b i ^ β i) = R := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [← hab i (Finset.mem_erase.mp hi).1]
  calc
    affineMonomial β a = a j ^ β j * R := by
      unfold affineMonomial R
      exact (Finset.mul_prod_erase Finset.univ (fun i => a i ^ β i)
        (Finset.mem_univ j)).symm
    _ ≤ b j ^ β j * R := mul_le_mul_of_nonneg_right hpow hRpos.le
    _ = affineMonomial β b := by
      unfold affineMonomial
      rw [← hrest]
      exact Finset.mul_prod_erase Finset.univ (fun i => b i ^ β i)
        (Finset.mem_univ j)

/-- Nonpositive exponents reverse the single-coordinate order. -/
theorem affineMonomial_coord_anti (β : ι → ℝ) (j : ι) (hβ : β j ≤ 0)
    {a b : ι → ℝ} (ha : a ∈ (positiveOrthant : Set (ι → ℝ)))
    (hb : b ∈ (positiveOrthant : Set (ι → ℝ)))
    (hab : ∀ i, i ≠ j → a i = b i) (haj : a j ≤ b j) :
    affineMonomial β b ≤ affineMonomial β a := by
  classical
  have hpow : b j ^ β j ≤ a j ^ β j :=
    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hβ (ha j) (hb j) haj
  let R : ℝ := ∏ i ∈ Finset.univ.erase j, a i ^ β i
  have hRpos : 0 < R := by
    apply Finset.prod_pos
    intro i hi
    exact Real.rpow_pos_of_pos (ha i) _
  have hrest : (∏ i ∈ Finset.univ.erase j, b i ^ β i) = R := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [← hab i (Finset.mem_erase.mp hi).1]
  calc
    affineMonomial β b = b j ^ β j * R := by
      unfold affineMonomial
      rw [← hrest]
      exact (Finset.mul_prod_erase Finset.univ (fun i => b i ^ β i)
        (Finset.mem_univ j)).symm
    _ ≤ a j ^ β j * R := mul_le_mul_of_nonneg_right hpow hRpos.le
    _ = affineMonomial β a := by
      unfold affineMonomial R
      exact Finset.mul_prod_erase Finset.univ (fun i => a i ^ β i)
        (Finset.mem_univ j)

/-- A strictly positive exponent makes the monomial strictly increasing in
that coordinate on the positive orthant. -/
theorem affineMonomial_coord_strictMono (β : ι → ℝ) (j : ι) (hβ : 0 < β j)
    {a b : ι → ℝ} (ha : a ∈ (positiveOrthant : Set (ι → ℝ)))
    (hb : b ∈ (positiveOrthant : Set (ι → ℝ)))
    (hab : ∀ i, i ≠ j → a i = b i) (haj : a j < b j) :
    affineMonomial β a < affineMonomial β b := by
  classical
  have hpow : a j ^ β j < b j ^ β j :=
    (Real.strictMonoOn_rpow_Ici_of_exponent_pos hβ)
      (le_of_lt (ha j)) (le_of_lt (hb j)) haj
  let R : ℝ := ∏ i ∈ Finset.univ.erase j, a i ^ β i
  have hRpos : 0 < R := by
    apply Finset.prod_pos
    intro i hi
    exact Real.rpow_pos_of_pos (ha i) _
  have hrest : (∏ i ∈ Finset.univ.erase j, b i ^ β i) = R := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [← hab i (Finset.mem_erase.mp hi).1]
  calc
    affineMonomial β a = a j ^ β j * R := by
      unfold affineMonomial R
      exact (Finset.mul_prod_erase Finset.univ (fun i => a i ^ β i)
        (Finset.mem_univ j)).symm
    _ < b j ^ β j * R := mul_lt_mul_of_pos_right hpow hRpos
    _ = affineMonomial β b := by
      unfold affineMonomial
      rw [← hrest]
      exact Finset.mul_prod_erase Finset.univ (fun i => b i ^ β i)
        (Finset.mem_univ j)

/-- A strictly negative exponent makes the monomial strictly decreasing in
that coordinate on the positive orthant. -/
theorem affineMonomial_coord_strictAnti (β : ι → ℝ) (j : ι) (hβ : β j < 0)
    {a b : ι → ℝ} (ha : a ∈ (positiveOrthant : Set (ι → ℝ)))
    (hb : b ∈ (positiveOrthant : Set (ι → ℝ)))
    (hab : ∀ i, i ≠ j → a i = b i) (haj : a j < b j) :
    affineMonomial β b < affineMonomial β a := by
  classical
  have hpow : b j ^ β j < a j ^ β j :=
    Real.strictAntiOn_rpow_Ioi_of_exponent_neg hβ (ha j) (hb j) haj
  let R : ℝ := ∏ i ∈ Finset.univ.erase j, a i ^ β i
  have hRpos : 0 < R := by
    apply Finset.prod_pos
    intro i hi
    exact Real.rpow_pos_of_pos (ha i) _
  have hrest : (∏ i ∈ Finset.univ.erase j, b i ^ β i) = R := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [← hab i (Finset.mem_erase.mp hi).1]
  calc
    affineMonomial β b = b j ^ β j * R := by
      unfold affineMonomial
      rw [← hrest]
      exact (Finset.mul_prod_erase Finset.univ (fun i => b i ^ β i)
        (Finset.mem_univ j)).symm
    _ < a j ^ β j * R := mul_lt_mul_of_pos_right hpow hRpos
    _ = affineMonomial β a := by
      unfold affineMonomial R
      exact Finset.mul_prod_erase Finset.univ (fun i => a i ^ β i)
        (Finset.mem_univ j)

/-! ## Exact one-dimensional calculus -/

/-- Logarithm of the affine monomial along a positive multiplicative line. -/
def monomialLogLine (β : ι → ℝ) (L : PositiveLineData ι) (lambda : ℝ) : ℝ :=
  ∑ i, β i * Real.log (lineRaw L lambda i)

/-- First logarithmic derivative along a positive multiplicative line. -/
def monomialLogLineFirst (β : ι → ℝ) (L : PositiveLineData ι)
    (lambda : ℝ) : ℝ :=
  ∑ i, β i * effectiveVelocity L lambda i

/-- The monomial itself along a positive multiplicative line. -/
def affineMonomialLine (β : ι → ℝ) (L : PositiveLineData ι)
    (lambda : ℝ) : ℝ :=
  affineMonomial β (lineRaw L lambda)

/-- First derivative expression for the monomial line. -/
def affineMonomialLineFirst (β : ι → ℝ) (L : PositiveLineData ι)
    (lambda : ℝ) : ℝ :=
  affineMonomialLine β L lambda * monomialLogLineFirst β L lambda

theorem affineMonomialLine_eq_exp (β : ι → ℝ) (L : PositiveLineData ι)
    {lambda : ℝ} (h : LinePositive L lambda) :
    affineMonomialLine β L lambda = Real.exp (monomialLogLine β L lambda) := by
  classical
  unfold affineMonomialLine affineMonomial monomialLogLine
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.rpow_def_of_pos (h i)]
  congr 1
  ring

theorem hasDerivAt_monomialLogLine (β : ι → ℝ) (L : PositiveLineData ι)
    {lambda : ℝ} (h : LinePositive L lambda) :
    HasDerivAt (monomialLogLine β L) (monomialLogLineFirst β L lambda) lambda := by
  classical
  unfold monomialLogLine monomialLogLineFirst
  apply HasDerivAt.fun_sum
  intro i _
  have hlog := (hasDerivAt_lineRaw L lambda i).log (ne_of_gt (h i))
  have heq : L.x i * L.u i / lineRaw L lambda i =
      effectiveVelocity L lambda i := by
    rw [← lineRaw_mul_effectiveVelocity L h i]
    field_simp [(h i).ne']
  simpa [heq] using hlog.const_mul (β i)

theorem hasDerivAt_monomialLogLineFirst (β : ι → ℝ)
    (L : PositiveLineData ι) {lambda : ℝ} (h : LinePositive L lambda) :
    HasDerivAt (monomialLogLineFirst β L)
      (-∑ i, β i * (effectiveVelocity L lambda i) ^ 2) lambda := by
  classical
  unfold monomialLogLineFirst
  have hs := HasDerivAt.fun_sum fun i (_hi : i ∈ Finset.univ) =>
    (hasDerivAt_effectiveVelocity L h i).const_mul (β i)
  apply hs.congr_deriv
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hasDerivAt_affineMonomialLine (β : ι → ℝ)
    (L : PositiveLineData ι) {lambda : ℝ} (h : LinePositive L lambda) :
    HasDerivAt (affineMonomialLine β L)
      (affineMonomialLineFirst β L lambda) lambda := by
  have hlog := (hasDerivAt_monomialLogLine β L h).exp
  have hevent : ∀ᶠ s in 𝓝 lambda, LinePositive L s :=
    (isOpen_setOf_linePositive L).mem_nhds h
  have heq : affineMonomialLine β L =ᶠ[𝓝 lambda]
      fun s => Real.exp (monomialLogLine β L s) :=
    hevent.mono fun s hs => affineMonomialLine_eq_exp β L hs
  apply (hlog.congr_of_eventuallyEq heq).congr_deriv
  rw [affineMonomialLineFirst, affineMonomialLine_eq_exp β L h]

theorem hasDerivAt_affineMonomialLineFirst (β : ι → ℝ)
    (L : PositiveLineData ι) {lambda : ℝ} (h : LinePositive L lambda) :
    HasDerivAt (affineMonomialLineFirst β L)
      (affineMonomialLine β L lambda *
        monomialCurvature β (effectiveVelocity L lambda)) lambda := by
  have hprod := (hasDerivAt_affineMonomialLine β L h).mul
    (hasDerivAt_monomialLogLineFirst β L h)
  apply hprod.congr_deriv
  unfold affineMonomialLineFirst monomialCurvature monomialLogLineFirst
  ring

/-- The monomial line is twice continuously differentiable on any region on
which all of its raw coordinates are positive. -/
theorem affineMonomialLine_contDiffOn (β : ι → ℝ)
    (L : PositiveLineData ι) :
    ContDiffOn ℝ 2 (affineMonomialLine β L) {s | LinePositive L s} := by
  classical
  have hlog : ContDiffOn ℝ 2 (monomialLogLine β L) {s | LinePositive L s} := by
    unfold monomialLogLine
    apply ContDiffOn.sum
    intro i _
    have hraw : ContDiff ℝ 2 (fun s => lineRaw L s i) := by
      unfold lineRaw
      fun_prop
    exact contDiffOn_const.mul
      (hraw.contDiffOn.log fun s hs => (hs i).ne')
  exact hlog.exp.congr fun s hs => affineMonomialLine_eq_exp β L hs

/-- Exact Hessian-line identity used in both curvature classifications. -/
theorem affineMonomialLine_secondDerivative (β : ι → ℝ)
    (L : PositiveLineData ι) {lambda : ℝ} (h : LinePositive L lambda) :
    secondDeriv (affineMonomialLine β L) lambda =
      affineMonomialLine β L lambda *
        monomialCurvature β (effectiveVelocity L lambda) := by
  unfold secondDeriv
  have hevent : ∀ᶠ s in 𝓝 lambda, LinePositive L s :=
    (isOpen_setOf_linePositive L).mem_nhds h
  have heq : (fun s => deriv (affineMonomialLine β L) s) =ᶠ[𝓝 lambda]
      affineMonomialLineFirst β L :=
    hevent.mono fun s hs => (hasDerivAt_affineMonomialLine β L hs).deriv
  exact ((hasDerivAt_affineMonomialLineFirst β L h).congr_of_eventuallyEq
    heq).deriv

/-! ## Curvature on the positive orthant -/

/-- Multiplicative line data representing the ordinary chord from `x` to
`y`. -/
def monomialChordLine (x y : ι → ℝ)
    (hx : x ∈ (positiveOrthant : Set (ι → ℝ))) : PositiveLineData ι where
  x := x
  u := fun i => (y i - x i) / x i
  x_pos := hx

omit [Fintype ι] in
theorem monomialChordLine_raw (x y : ι → ℝ)
    (hx : x ∈ (positiveOrthant : Set (ι → ℝ))) (s : ℝ) :
    lineRaw (monomialChordLine x y hx) s =
      (1 - s) • x + s • y := by
  funext i
  simp only [lineRaw, monomialChordLine, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  field_simp [(hx i).ne']
  ring

omit [Fintype ι] in
theorem monomialChordLine_positive (x y : ι → ℝ)
    (hx : x ∈ (positiveOrthant : Set (ι → ℝ)))
    (hy : y ∈ (positiveOrthant : Set (ι → ℝ)))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    LinePositive (monomialChordLine x y hx) s := by
  intro i
  rw [show lineRaw (monomialChordLine x y hx) s i =
      (1 - s) * x i + s * y i by
    simpa [Pi.smul_apply] using congrFun (monomialChordLine_raw x y hx s) i]
  rcases hs.1.eq_or_lt with rfl | hspos
  · simpa using hx i
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr hs.2) (hx i).le)
      (mul_pos hspos (hy i))

/-- Nonnegative affine exponents give a concave monomial on the positive
orthant. -/
theorem affineMonomial_concaveOn_of_nonneg (β : ι → ℝ)
    (hsum : IsAffineFamily β) (hβ : ∀ i, 0 ≤ β i) :
    ConcaveOn ℝ (positiveOrthant : Set (ι → ℝ)) (affineMonomial β) := by
  refine ⟨positiveOrthant_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  let L := monomialChordLine x y hx
  have hline : ∀ s ∈ Icc (0 : ℝ) 1, LinePositive L s := by
    intro s hs
    exact monomialChordLine_positive x y hx hy hs
  have hcont : ContinuousOn (affineMonomialLine β L) (Icc (0 : ℝ) 1) := by
    intro s hs
    exact (hasDerivAt_affineMonomialLine β L (hline s hs)).continuousAt.continuousWithinAt
  have hfirst : ∀ s ∈ interior (Icc (0 : ℝ) 1),
      HasDerivWithinAt (affineMonomialLine β L)
        (affineMonomialLineFirst β L s) (interior (Icc (0 : ℝ) 1)) s := by
    intro s hs
    exact (hasDerivAt_affineMonomialLine β L
      (hline s (interior_subset hs))).hasDerivWithinAt
  have hsecond : ∀ s ∈ interior (Icc (0 : ℝ) 1),
      HasDerivWithinAt (affineMonomialLineFirst β L)
        (affineMonomialLine β L s *
          monomialCurvature β (effectiveVelocity L s))
        (interior (Icc (0 : ℝ) 1)) s := by
    intro s hs
    exact (hasDerivAt_affineMonomialLineFirst β L
      (hline s (interior_subset hs))).hasDerivWithinAt
  have hsign : ∀ s ∈ interior (Icc (0 : ℝ) 1),
      affineMonomialLine β L s *
          monomialCurvature β (effectiveVelocity L s) ≤ 0 := by
    intro s hs
    exact mul_nonpos_of_nonneg_of_nonpos
      (affineMonomial_pos β (hline s (interior_subset hs))).le
      (monomialCurvature_nonpos_of_nonneg β _ hβ hsum)
  have hscalar : ConcaveOn ℝ (Icc (0 : ℝ) 1) (affineMonomialLine β L) :=
    concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (0 : ℝ) 1)
      hcont hfirst hsecond hsign
  have hb_le_one : b ≤ 1 := by linarith
  have hineq := hscalar.2 (show (0 : ℝ) ∈ Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Icc 0 1 by simp) (sub_nonneg.mpr hb_le_one) hb (by ring)
  have ha_eq : a = 1 - b := by linarith
  simpa [L, affineMonomialLine, monomialChordLine_raw, ha_eq] using hineq

/-- A unique positive affine exponent and nonpositive remaining exponents give
a convex monomial on the positive orthant. -/
theorem affineMonomial_convexOn_of_uniquePositive (β : ι → ℝ)
    (hsum : IsAffineFamily β) (hunique : HasUniquePositive β) :
    ConvexOn ℝ (positiveOrthant : Set (ι → ℝ)) (affineMonomial β) := by
  refine ⟨positiveOrthant_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  let L := monomialChordLine x y hx
  have hline : ∀ s ∈ Icc (0 : ℝ) 1, LinePositive L s := by
    intro s hs
    exact monomialChordLine_positive x y hx hy hs
  have hcont : ContinuousOn (affineMonomialLine β L) (Icc (0 : ℝ) 1) := by
    intro s hs
    exact (hasDerivAt_affineMonomialLine β L (hline s hs)).continuousAt.continuousWithinAt
  have hfirst : ∀ s ∈ interior (Icc (0 : ℝ) 1),
      HasDerivWithinAt (affineMonomialLine β L)
        (affineMonomialLineFirst β L s) (interior (Icc (0 : ℝ) 1)) s := by
    intro s hs
    exact (hasDerivAt_affineMonomialLine β L
      (hline s (interior_subset hs))).hasDerivWithinAt
  have hsecond : ∀ s ∈ interior (Icc (0 : ℝ) 1),
      HasDerivWithinAt (affineMonomialLineFirst β L)
        (affineMonomialLine β L s *
          monomialCurvature β (effectiveVelocity L s))
        (interior (Icc (0 : ℝ) 1)) s := by
    intro s hs
    exact (hasDerivAt_affineMonomialLineFirst β L
      (hline s (interior_subset hs))).hasDerivWithinAt
  have hsign : ∀ s ∈ interior (Icc (0 : ℝ) 1),
      0 ≤ affineMonomialLine β L s *
          monomialCurvature β (effectiveVelocity L s) := by
    intro s hs
    exact mul_nonneg
      (affineMonomial_pos β (hline s (interior_subset hs))).le
      (monomialCurvature_nonneg_of_uniquePositive β _ hsum hunique)
  have hscalar : ConvexOn ℝ (Icc (0 : ℝ) 1) (affineMonomialLine β L) :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (0 : ℝ) 1)
      hcont hfirst hsecond hsign
  have hb_le_one : b ≤ 1 := by linarith
  have hineq := hscalar.2 (show (0 : ℝ) ∈ Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Icc 0 1 by simp) (sub_nonneg.mpr hb_le_one) hb (by ring)
  have ha_eq : a = 1 - b := by linarith
  simpa [L, affineMonomialLine, monomialChordLine_raw, ha_eq] using hineq

/-! ## Converse curvature tests -/

omit [Fintype ι] in
theorem lineRaw_combo (L : PositiveLineData ι) (s t a b : ℝ)
    (hab : a + b = 1) :
    lineRaw L (a * s + b * t) =
      a • lineRaw L s + b • lineRaw L t := by
  funext i
  simp only [lineRaw, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [show b = 1 - a by linarith]
  ring

theorem affineMonomialLine_concaveOn_of_concave
    (β : ι → ℝ) (L : PositiveLineData ι)
    {U : Set ℝ} (hU : Convex ℝ U)
    (hpos : ∀ s ∈ U, LinePositive L s)
    (hconc : ConcaveOn ℝ (positiveOrthant : Set (ι → ℝ))
      (affineMonomial β)) :
    ConcaveOn ℝ U (affineMonomialLine β L) := by
  refine ⟨hU, ?_⟩
  intro s hs t ht a b ha hb hab
  have h := hconc.2 (hpos s hs) (hpos t ht) ha hb hab
  simpa [affineMonomialLine, lineRaw_combo L s t a b hab] using h

theorem affineMonomialLine_convexOn_of_convex
    (β : ι → ℝ) (L : PositiveLineData ι)
    {U : Set ℝ} (hU : Convex ℝ U)
    (hpos : ∀ s ∈ U, LinePositive L s)
    (hconv : ConvexOn ℝ (positiveOrthant : Set (ι → ℝ))
      (affineMonomial β)) :
    ConvexOn ℝ U (affineMonomialLine β L) := by
  refine ⟨hU, ?_⟩
  intro s hs t ht a b ha hb hab
  have h := hconv.2 (hpos s hs) (hpos t ht) ha hb hab
  simpa [affineMonomialLine, lineRaw_combo L s t a b hab] using h

/-- The line through the all-ones point with arbitrary logarithmic velocity. -/
def standardMonomialLine (z : ι → ℝ) : PositiveLineData ι where
  x := fun _ => 1
  u := z
  x_pos := fun _ => zero_lt_one

omit [Fintype ι] in
@[simp] theorem standardMonomialLine_raw (z : ι → ℝ) (s : ℝ) (i : ι) :
    lineRaw (standardMonomialLine z) s i = 1 + z i * s := by
  simp [standardMonomialLine, lineRaw]

omit [Fintype ι] in
@[simp] theorem standardMonomialLine_effectiveVelocity_zero
    (z : ι → ℝ) (i : ι) :
    effectiveVelocity (standardMonomialLine z) 0 i = z i := by
  simp [standardMonomialLine, effectiveVelocity]

theorem affineMonomial_curvature_nonpos_of_concave (β : ι → ℝ)
    (hconc : ConcaveOn ℝ (positiveOrthant : Set (ι → ℝ))
      (affineMonomial β)) :
    ∀ z : ι → ℝ, monomialCurvature β z ≤ 0 := by
  intro z
  let L := standardMonomialLine z
  have hopen : IsOpen {s : ℝ | LinePositive L s} := isOpen_setOf_linePositive L
  have hzero : (0 : ℝ) ∈ {s : ℝ | LinePositive L s} := linePositiveZero L
  obtain ⟨eps, heps, hball⟩ : ∃ eps > 0,
      Metric.ball (0 : ℝ) eps ⊆ {s : ℝ | LinePositive L s} :=
    Metric.isOpen_iff.mp hopen 0 hzero
  have hsubset : Ioo (-eps) eps ⊆ {s : ℝ | LinePositive L s} := by
    simpa only [Real.ball_zero_eq_Ioo] using hball
  have hscalar : ConcaveOn ℝ (Ioo (-eps) eps) (affineMonomialLine β L) :=
    affineMonomialLine_concaveOn_of_concave β L (convex_Ioo _ _)
      (fun s hs => hsubset hs) hconc
  have hsmooth : ContDiffOn ℝ 2 (affineMonomialLine β L) (Ioo (-eps) eps) :=
    (affineMonomialLine_contDiffOn β L).mono hsubset
  have hsecond := concaveOn_secondDeriv_nonpos heps hsmooth hscalar
  rw [affineMonomialLine_secondDerivative β L (linePositiveZero L)] at hsecond
  have heff : effectiveVelocity L 0 = z := by
    funext i
    simp [L, standardMonomialLine, effectiveVelocity]
  rw [heff] at hsecond
  simpa [L, affineMonomialLine, affineMonomial, standardMonomialLine,
    effectiveVelocity, lineRaw] using hsecond

theorem affineMonomial_curvature_nonneg_of_convex (β : ι → ℝ)
    (hconv : ConvexOn ℝ (positiveOrthant : Set (ι → ℝ))
      (affineMonomial β)) :
    ∀ z : ι → ℝ, 0 ≤ monomialCurvature β z := by
  intro z
  let L := standardMonomialLine z
  have hopen : IsOpen {s : ℝ | LinePositive L s} := isOpen_setOf_linePositive L
  have hzero : (0 : ℝ) ∈ {s : ℝ | LinePositive L s} := linePositiveZero L
  obtain ⟨eps, heps, hball⟩ : ∃ eps > 0,
      Metric.ball (0 : ℝ) eps ⊆ {s : ℝ | LinePositive L s} :=
    Metric.isOpen_iff.mp hopen 0 hzero
  have hsubset : Ioo (-eps) eps ⊆ {s : ℝ | LinePositive L s} := by
    simpa only [Real.ball_zero_eq_Ioo] using hball
  have hscalar : ConvexOn ℝ (Ioo (-eps) eps) (affineMonomialLine β L) :=
    affineMonomialLine_convexOn_of_convex β L (convex_Ioo _ _)
      (fun s hs => hsubset hs) hconv
  have hsmooth : ContDiffOn ℝ 2 (affineMonomialLine β L) (Ioo (-eps) eps) :=
    (affineMonomialLine_contDiffOn β L).mono hsubset
  have hsecond := convexOn_secondDeriv_nonneg heps hsmooth hscalar
  rw [affineMonomialLine_secondDerivative β L (linePositiveZero L)] at hsecond
  have heff : effectiveVelocity L 0 = z := by
    funext i
    simp [L, standardMonomialLine, effectiveVelocity]
  rw [heff] at hsecond
  simpa [L, affineMonomialLine, affineMonomial, standardMonomialLine,
    effectiveVelocity, lineRaw] using hsecond

/-- Two distinct positive affine exponents produce a direction of strictly
negative monomial curvature. -/
theorem monomialCurvature_neg_of_two_positive (β : ι → ℝ)
    {i j : ι} (hij : i ≠ j) (hi : 0 < β i) (hj : 0 < β j) :
    ∃ z : ι → ℝ, monomialCurvature β z < 0 := by
  classical
  have hji : j ≠ i := Ne.symm hij
  let z : ι → ℝ := fun k =>
    if k = i then 1 / β i else if k = j then -(1 / β j) else 0
  have sum_two (f : ι → ℝ)
      (hf : ∀ k, k ≠ i → k ≠ j → f k = 0) :
      ∑ k, f k = f i + f j := by
    calc
      (∑ k, f k) = ∑ k ∈ ({i, j} : Finset ι), f k := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro k _ hk
        have hk' : k ≠ i ∧ k ≠ j := by simpa using hk
        exact hf k hk'.1 hk'.2
      _ = f i + f j := by simp [hij]
  have hlinear : ∑ k, β k * z k = 0 := by
    rw [sum_two (fun k => β k * z k)]
    · simp [z, hji, hi.ne', hj.ne']
    · intro k hki hkj
      simp [z, hki, hkj]
  have hquadratic : ∑ k, β k * z k ^ 2 = 1 / β i + 1 / β j := by
    rw [sum_two (fun k => β k * z k ^ 2)]
    · simp [z, hji]
      field_simp [hi.ne', hj.ne']
    · intro k hki hkj
      simp [z, hki, hkj]
  refine ⟨z, ?_⟩
  unfold monomialCurvature
  rw [hlinear, hquadratic]
  have hpos : 0 < 1 / β i + 1 / β j :=
    add_pos (one_div_pos.mpr hi) (one_div_pos.mpr hj)
  nlinarith

/-- Exact concavity classification of an affine monomial. -/
theorem affineMonomial_concaveOn_iff (β : ι → ℝ)
    (hsum : IsAffineFamily β) :
    ConcaveOn ℝ (positiveOrthant : Set (ι → ℝ)) (affineMonomial β) ↔
      ∀ i, 0 ≤ β i := by
  constructor
  · intro hconc i
    exact (coefficient_mem_Icc_of_curvature_nonpos β
      (affineMonomial_curvature_nonpos_of_concave β hconc) i).1
  · exact affineMonomial_concaveOn_of_nonneg β hsum

/-- Exact convexity classification of an affine monomial. -/
theorem affineMonomial_convexOn_iff (β : ι → ℝ)
    (hsum : IsAffineFamily β) :
    ConvexOn ℝ (positiveOrthant : Set (ι → ℝ)) (affineMonomial β) ↔
      HasUniquePositive β := by
  constructor
  · intro hconv
    have hcurv := affineMonomial_curvature_nonneg_of_convex β hconv
    have hpositive : ∃ k, 0 < β k := by
      by_contra hnone
      simp only [not_exists, not_lt] at hnone
      have hnonpos : ∑ k, β k ≤ 0 := Finset.sum_nonpos fun k _ => hnone k
      have hsum' : ∑ k, β k = 1 := hsum
      linarith
    obtain ⟨k, hk⟩ := hpositive
    refine ⟨k, hk, ?_⟩
    intro j hj
    by_contra hjnonpos
    have hjpos : 0 < β j := lt_of_not_ge hjnonpos
    obtain ⟨z, hzneg⟩ := monomialCurvature_neg_of_two_positive β
      (Ne.symm hj) hk hjpos
    exact (not_lt_of_ge (hcurv z)) hzneg
  · exact affineMonomial_convexOn_of_uniquePositive β hsum

/-- The literal six-way monomial package from the blueprint. -/
theorem affineMonomialCurvaturePackage (β : ι → ℝ)
    (hsum : IsAffineFamily β) :
    (ConcaveOn ℝ (positiveOrthant : Set (ι → ℝ)) (affineMonomial β) ↔
      ∀ i, 0 ≤ β i) ∧
    (ConvexOn ℝ (positiveOrthant : Set (ι → ℝ)) (affineMonomial β) ↔
      HasUniquePositive β) ∧
    (∀ j, 0 ≤ β j → ∀ a ∈ (positiveOrthant : Set (ι → ℝ)),
      ∀ b ∈ (positiveOrthant : Set (ι → ℝ)),
        (∀ i, i ≠ j → a i = b i) → a j ≤ b j →
          affineMonomial β a ≤ affineMonomial β b) ∧
    (∀ j, β j ≤ 0 → ∀ a ∈ (positiveOrthant : Set (ι → ℝ)),
      ∀ b ∈ (positiveOrthant : Set (ι → ℝ)),
        (∀ i, i ≠ j → a i = b i) → a j ≤ b j →
          affineMonomial β b ≤ affineMonomial β a) ∧
    (∀ j, 0 < β j → ∀ a ∈ (positiveOrthant : Set (ι → ℝ)),
      ∀ b ∈ (positiveOrthant : Set (ι → ℝ)),
        (∀ i, i ≠ j → a i = b i) → a j < b j →
          affineMonomial β a < affineMonomial β b) ∧
    (∀ j, β j < 0 → ∀ a ∈ (positiveOrthant : Set (ι → ℝ)),
      ∀ b ∈ (positiveOrthant : Set (ι → ℝ)),
        (∀ i, i ≠ j → a i = b i) → a j < b j →
          affineMonomial β b < affineMonomial β a) := by
  exact ⟨affineMonomial_concaveOn_iff β hsum,
    affineMonomial_convexOn_iff β hsum,
    fun j hj a ha b hb hab haj => affineMonomial_coord_mono β j hj ha hb hab haj,
    fun j hj a ha b hb hab haj => affineMonomial_coord_anti β j hj ha hb hab haj,
    fun j hj a ha b hb hab haj => affineMonomial_coord_strictMono β j hj ha hb hab haj,
    fun j hj a ha b hb hab haj => affineMonomial_coord_strictAnti β j hj ha hb hab haj⟩

end ConditionalEntropy
