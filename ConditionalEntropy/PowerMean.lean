import ConditionalEntropy.FiniteData
import ConditionalEntropy.ParamMeasure
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Finite Holder and compactified power means
-/

noncomputable section

open Set
open scoped BigOperators ENNReal NNReal

namespace ConditionalEntropy

universe u

/-- The nonnegative finite `L^a` expression used in the Renyi factorization. -/
def lpNorm {I : Type u} [Fintype I] (a : ℝ) (x : ConeVec I) : ℝ :=
  (∑ i, x.1 i ^ a) ^ (1 / a)

/-- Total compactified power mean.  The value at order zero is the mass, and
the value at the top endpoint is the finite maximum. -/
def parameterPowerMean {I : Type u} [Fintype I] [Nonempty I]
    (a : Param) (x : ConeVec I) : ℝ :=
  if htop : a = ⊤ then finMax x.1
  else
    let r := paramToReal a htop
    if r = 0 then l1Mass x.1 else lpNorm r x

/-- Finite Holder inequality in the exact real-valued form used by the
power-mean curvature proof. -/
theorem finiteHolder {I : Type u} [Fintype I]
    {p q : ℝ} (hp : 1 < p) (_hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1)
    (a b : I → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∑ i, a i * b i) ≤
      (∑ i, a i ^ p) ^ (1 / p) * (∑ i, b i ^ q) ^ (1 / q) := by
  have hpq' : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    exact ⟨hp, by simpa only [one_div] using hpq⟩
  exact Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hpq'
    (fun i _ => ha i) (fun i _ => hb i)

/-- Positive homogeneity of the finite `L^a` expression. -/
theorem lpNorm_coneScale {I : Type u} [Fintype I]
    {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (x : ConeVec I) :
    lpNorm a (coneScale c hc x) = c * lpNorm a x := by
  have hsum : 0 ≤ ∑ i, x.1 i ^ a :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (x.2 i) _
  unfold lpNorm
  simp only [coneScale]
  calc
    (∑ i, (c * x.1 i) ^ a) ^ (1 / a) =
        (c ^ a * ∑ i, x.1 i ^ a) ^ (1 / a) := by
      congr 1
      simp_rw [Real.mul_rpow hc (x.2 _)]
      rw [Finset.mul_sum]
    _ = (c ^ a) ^ (1 / a) * (∑ i, x.1 i ^ a) ^ (1 / a) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hc _) hsum]
    _ = c * (∑ i, x.1 i ^ a) ^ (1 / a) := by
      have hinv : 1 / a = a⁻¹ := one_div a
      rw [hinv, Real.rpow_rpow_inv hc ha.ne']

/-- The finite power mean is nonnegative. -/
theorem lpNorm_nonneg {I : Type u} [Fintype I]
    (a : ℝ) (x : ConeVec I) : 0 ≤ lpNorm a x := by
  unfold lpNorm
  exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (x.2 i) a) (1 / a)

/-- For a positive order, the finite power mean vanishes exactly at the
origin of the nonnegative cone. -/
theorem lpNorm_eq_zero_iff {I : Type u} [Fintype I]
    {a : ℝ} (ha : 0 < a) (x : ConeVec I) : lpNorm a x = 0 ↔ x = 0 := by
  have hpow_nonneg : ∀ i : I, 0 ≤ x.1 i ^ a := fun i =>
    Real.rpow_nonneg (x.2 i) a
  have hsum_nonneg : 0 ≤ ∑ i, x.1 i ^ a :=
    Finset.sum_nonneg fun i _ => hpow_nonneg i
  constructor
  · intro hnorm
    have hsum : (∑ i, x.1 i ^ a) = 0 :=
      ((Real.rpow_eq_zero_iff_of_nonneg hsum_nonneg).mp hnorm).1
    apply Subtype.ext
    funext i
    have hi : x.1 i ^ a = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hpow_nonneg j).mp hsum i
        (Finset.mem_univ i)
    exact ((Real.rpow_eq_zero_iff_of_nonneg (x.2 i)).mp hi).1
  · rintro rfl
    simp [lpNorm, ha.ne']

/-- Reverse Minkowski inequality for nonnegative finite vectors at an order
strictly between zero and one. -/
theorem lpNorm_add_le_reverse {I : Type u} [Fintype I]
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (x z : ConeVec I) :
    lpNorm a x + lpNorm a z ≤ lpNorm a (x + z) := by
  let A : ℝ := lpNorm a x
  let B : ℝ := lpNorm a z
  have hA0 : 0 ≤ A := lpNorm_nonneg a x
  have hB0 : 0 ≤ B := lpNorm_nonneg a z
  by_cases hAzero : A = 0
  · have hxzero : x = 0 := (lpNorm_eq_zero_iff ha0 x).mp hAzero
    subst x
    simp [A, hAzero]
  by_cases hBzero : B = 0
  · have hzzero : z = 0 := (lpNorm_eq_zero_iff ha0 z).mp hBzero
    subst z
    simp [B, hBzero]
  have hA : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAzero)
  have hB : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hBzero)
  let C : ℝ := A + B
  have hC : 0 < C := add_pos hA hB
  let theta : ℝ := A / C
  have htheta0 : 0 ≤ theta := div_nonneg hA.le hC.le
  have htheta1 : theta ≤ 1 := (div_le_one hC).2 (le_add_of_nonneg_right hB.le)
  have honeTheta : 1 - theta = B / C := by
    dsimp [theta, C]
    field_simp
    ring
  let xN : ConeVec I := coneScale (1 / A) (one_div_nonneg.mpr hA.le) x
  let zN : ConeVec I := coneScale (1 / B) (one_div_nonneg.mpr hB.le) z
  have hxNnorm : lpNorm a xN = 1 := by
    rw [show xN = coneScale (1 / A) (one_div_nonneg.mpr hA.le) x by rfl,
      lpNorm_coneScale ha0 (one_div_nonneg.mpr hA.le)]
    simpa [A, div_eq_mul_inv, mul_comm] using (div_self hAzero)
  have hzNnorm : lpNorm a zN = 1 := by
    rw [show zN = coneScale (1 / B) (one_div_nonneg.mpr hB.le) z by rfl,
      lpNorm_coneScale ha0 (one_div_nonneg.mpr hB.le)]
    simpa [B, div_eq_mul_inv, mul_comm] using (div_self hBzero)
  have hxNsum : (∑ i, xN.1 i ^ a) = 1 := by
    have hsum0 : 0 ≤ ∑ i, xN.1 i ^ a :=
      Finset.sum_nonneg fun i _ => Real.rpow_nonneg (xN.2 i) a
    have h := congrArg (fun t : ℝ => t ^ a) hxNnorm
    simpa [lpNorm, one_div, Real.rpow_inv_rpow hsum0 ha0.ne'] using h
  have hzNsum : (∑ i, zN.1 i ^ a) = 1 := by
    have hsum0 : 0 ≤ ∑ i, zN.1 i ^ a :=
      Finset.sum_nonneg fun i _ => Real.rpow_nonneg (zN.2 i) a
    have h := congrArg (fun t : ℝ => t ^ a) hzNnorm
    simpa [lpNorm, one_div, Real.rpow_inv_rpow hsum0 ha0.ne'] using h
  let w : ConeVec I := coneMix theta ⟨htheta0, htheta1⟩ xN zN
  have hcoord : ∀ i : I,
      theta * (xN.1 i ^ a) + (1 - theta) * (zN.1 i ^ a) ≤ w.1 i ^ a := by
    intro i
    have hconc := (Real.concaveOn_rpow ha0.le ha1.le).2
      (xN.2 i) (zN.2 i) htheta0 (sub_nonneg.mpr htheta1)
      (by ring : theta + (1 - theta) = 1)
    simpa [w, coneMix, smul_eq_mul] using hconc
  have hsumw : 1 ≤ ∑ i, w.1 i ^ a := by
    have hsum :
        (∑ i : I, (theta * (xN.1 i ^ a) +
          (1 - theta) * (zN.1 i ^ a))) ≤ ∑ i : I, w.1 i ^ a :=
      Finset.sum_le_sum fun i _ => hcoord i
    calc
      1 = theta * (∑ i, xN.1 i ^ a) +
          (1 - theta) * (∑ i, zN.1 i ^ a) := by rw [hxNsum, hzNsum]; ring
      _ = ∑ i, (theta * (xN.1 i ^ a) +
          (1 - theta) * (zN.1 i ^ a)) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ ∑ i, w.1 i ^ a := hsum
  have hwnorm : 1 ≤ lpNorm a w := by
    have hexp : 0 ≤ 1 / a := (one_div_pos.mpr ha0).le
    have hr := Real.rpow_le_rpow (by norm_num : 0 ≤ (1 : ℝ)) hsumw hexp
    simpa [lpNorm] using hr
  have hscale : coneScale C hC.le w = x + z := by
    apply Subtype.ext
    funext i
    dsimp [w, xN, zN, theta, C, coneScale, coneMix]
    field_simp
    ring
  calc
    lpNorm a x + lpNorm a z = C := rfl
    _ = C * 1 := (mul_one C).symm
    _ ≤ C * lpNorm a w := mul_le_mul_of_nonneg_left hwnorm hC.le
    _ = lpNorm a (coneScale C hC.le w) :=
      (lpNorm_coneScale ha0 hC.le w).symm
    _ = lpNorm a (x + z) := by rw [hscale]

/-- Concavity of the finite power mean for orders strictly between zero and
one. -/
theorem lpNorm_concaveCone {I : Type u} [Fintype I]
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ConcaveCone (fun x : ConeVec I => lpNorm a x) := by
  intro x z lambda hlambda
  let sx : ConeVec I := coneScale lambda hlambda.1 x
  let sz : ConeVec I := coneScale (1 - lambda) (sub_nonneg.mpr hlambda.2) z
  have hadd := lpNorm_add_le_reverse ha0 ha1 sx sz
  rw [show sx = coneScale lambda hlambda.1 x by rfl,
    show sz = coneScale (1 - lambda) (sub_nonneg.mpr hlambda.2) z by rfl,
    lpNorm_coneScale ha0 hlambda.1,
    lpNorm_coneScale ha0 (sub_nonneg.mpr hlambda.2)] at hadd
  have hsum : sx + sz = coneMix lambda hlambda x z := by
    apply Subtype.ext
    rfl
  rw [hsum] at hadd
  exact hadd

/-- Cone mass is affine, hence both concave and convex. -/
theorem l1Mass_concave_convex {I : Type u} [Fintype I] :
    ConcaveCone (fun x : ConeVec I => l1Mass x.1) ∧
      ConvexCone (fun x : ConeVec I => l1Mass x.1) := by
  have haffine : ∀ (x z : ConeVec I) (lambda : ℝ)
      (hlambda : lambda ∈ Icc (0 : ℝ) 1),
      l1Mass (coneMix lambda hlambda x z).1 =
        lambda * l1Mass x.1 + (1 - lambda) * l1Mass z.1 := by
    intro x z lambda hlambda
    simp [l1Mass, coneMix, Finset.sum_add_distrib, Finset.mul_sum]
  constructor
  · intro x z lambda hlambda
    exact (haffine x z lambda hlambda).ge
  · intro x z lambda hlambda
    exact (haffine x z lambda hlambda).le

/-- Minkowski's inequality gives cone convexity for every order at least one. -/
theorem lpNorm_convexCone {I : Type u} [Fintype I]
    {a : ℝ} (ha : 1 ≤ a) : ConvexCone (fun x : ConeVec I => lpNorm a x) := by
  have haPos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  intro x z lambda hlambda
  have h := Real.Lp_add_le (s := Finset.univ)
    (f := fun i => lambda * x.1 i)
    (g := fun i => (1 - lambda) * z.1 i) ha
  have h' : lpNorm a (coneMix lambda hlambda x z) ≤
      lpNorm a (coneScale lambda hlambda.1 x) +
        lpNorm a (coneScale (1 - lambda) (sub_nonneg.mpr hlambda.2) z) := by
    simpa only [lpNorm, coneMix, coneScale,
      abs_of_nonneg (mul_nonneg hlambda.1 (x.2 _)),
      abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hlambda.2) (z.2 _)),
      abs_of_nonneg (add_nonneg (mul_nonneg hlambda.1 (x.2 _))
        (mul_nonneg (sub_nonneg.mpr hlambda.2) (z.2 _)))] using h
  rw [lpNorm_coneScale haPos hlambda.1,
    lpNorm_coneScale haPos (sub_nonneg.mpr hlambda.2)] at h'
  exact h'

/-- The finite maximum is convex on the nonnegative cone. -/
theorem finMax_convexCone {I : Type u} [Fintype I] [Nonempty I] :
    ConvexCone (fun x : ConeVec I => finMax x.1) := by
  intro x z lambda hlambda
  unfold finMax
  apply Finset.sup'_le Finset.univ_nonempty
  intro i _hi
  have hx : x.1 i ≤ Finset.univ.sup' Finset.univ_nonempty x.1 := by
    exact Finset.le_sup' (f := x.1) (Finset.mem_univ i)
  have hz : z.1 i ≤ Finset.univ.sup' Finset.univ_nonempty z.1 := by
    exact Finset.le_sup' (f := z.1) (Finset.mem_univ i)
  exact add_le_add
    (mul_le_mul_of_nonneg_left hx hlambda.1)
    (mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr hlambda.2))

/-- The manuscript's three-part finite power-curvature statement. -/
theorem powerCurvature {I : Type u} [Fintype I] [Nonempty I] :
    (∀ a : ℝ, 0 < a → a < 1 →
      ConcaveCone (fun x : ConeVec I => lpNorm a x)) ∧
    (∀ a : ℝ, 1 ≤ a →
      ConvexCone (fun x : ConeVec I => lpNorm a x)) ∧
    ConvexCone (fun x : ConeVec I => finMax x.1) := by
  exact ⟨fun _ => lpNorm_concaveCone, fun _ => lpNorm_convexCone,
    finMax_convexCone⟩

@[simp] theorem parameterPowerMean_top {I : Type u} [Fintype I] [Nonempty I]
    (x : ConeVec I) : parameterPowerMean (⊤ : Param) x = finMax x.1 := by
  simp [parameterPowerMean]

@[simp] theorem parameterPowerMean_zero {I : Type u} [Fintype I] [Nonempty I]
    (x : ConeVec I) : parameterPowerMean (0 : Param) x = l1Mass x.1 := by
  have hzero : paramToReal (0 : Param) WithTop.zero_ne_top = 0 := by
    change ENNReal.toReal (0 : ENNReal) = 0
    exact ENNReal.toReal_zero
  rw [parameterPowerMean]
  simp only [WithTop.zero_ne_top, ↓reduceDIte]
  rw [hzero]
  simp

theorem parameterPowerMean_finite {I : Type u} [Fintype I] [Nonempty I]
    {a : ℝ} (ha : 0 ≤ a) (ha0 : a ≠ 0) (x : ConeVec I) :
    parameterPowerMean (finiteParam a) x = lpNorm a x := by
  simp [parameterPowerMean, finiteParam_ne_top, paramToReal_finiteParam ha, ha0]

/-- Evaluation at a finite nonnegative-real parameter. -/
@[simp] theorem parameterPowerMean_coeNNReal {I : Type u} [Fintype I] [Nonempty I]
    (q : NNReal) (x : ConeVec I) :
    parameterPowerMean (q : Param) x =
      if (q : ℝ) = 0 then l1Mass x.1 else lpNorm (q : ℝ) x := by
  rw [parameterPowerMean]
  simp only [WithTop.coe_ne_top, ↓reduceDIte]
  rfl

/-- The compactified parameter bridge: lower orders are concave, upper
orders (including top) are convex, and every nonzero cone vector has a
strictly positive power mean. -/
theorem parameterPowerCurvature {I : Type u} [Fintype I] [Nonempty I] :
    (∀ a : Param, a < 1 →
      ConcaveCone (fun x : ConeVec I => parameterPowerMean a x)) ∧
    (∀ a : Param, 1 ≤ a →
      ConvexCone (fun x : ConeVec I => parameterPowerMean a x)) ∧
    (∀ (a : Param) (x : ConeVec I), x ≠ 0 → 0 < parameterPowerMean a x) := by
  constructor
  · intro a ha
    induction a using WithTop.recTopCoe with
    | top => simp at ha
    | coe q =>
        have hq1 : (q : ℝ) < 1 := by exact_mod_cast ha
        by_cases hq0 : (q : ℝ) = 0
        · have heq :
              (fun x : ConeVec I => parameterPowerMean (q : Param) x) =
                fun x : ConeVec I => l1Mass x.1 := by
              funext x
              rw [parameterPowerMean_coeNNReal, if_pos hq0]
          rw [heq]
          exact (l1Mass_concave_convex (I := I)).1
        · have hqpos : 0 < (q : ℝ) :=
            lt_of_le_of_ne q.2 (Ne.symm hq0)
          have heq :
              (fun x : ConeVec I => parameterPowerMean (q : Param) x) =
                fun x : ConeVec I => lpNorm (q : ℝ) x := by
              funext x
              rw [parameterPowerMean_coeNNReal, if_neg hq0]
          rw [heq]
          exact lpNorm_concaveCone (I := I) hqpos hq1
  constructor
  · intro a ha
    induction a using WithTop.recTopCoe with
    | top => simpa using (finMax_convexCone (I := I))
    | coe q =>
        have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast ha
        have hq0 : (q : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hq1)
        have heq :
            (fun x : ConeVec I => parameterPowerMean (q : Param) x) =
              fun x : ConeVec I => lpNorm (q : ℝ) x := by
            funext x
            rw [parameterPowerMean_coeNNReal, if_neg hq0]
        rw [heq]
        exact lpNorm_convexCone (I := I) hq1
  · intro a x hx
    induction a using WithTop.recTopCoe with
    | top =>
        obtain ⟨i, hi⟩ := finMax_mem x.1
        have hex : ∃ j : I, 0 < x.1 j := by
          by_contra hnone
          apply hx
          apply Subtype.ext
          funext j
          exact le_antisymm (not_lt.mp (not_exists.mp hnone j)) (x.2 j)
        obtain ⟨j, hj⟩ := hex
        have hjmax : x.1 j ≤ finMax x.1 := by
          unfold finMax
          exact Finset.le_sup' (f := x.1) (Finset.mem_univ j)
        simpa using hj.trans_le hjmax
    | coe q =>
        by_cases hq0 : (q : ℝ) = 0
        · rw [parameterPowerMean_coeNNReal, if_pos hq0]
          exact (coneNonzeroMass x).mp hx
        · have hqpos : 0 < (q : ℝ) :=
            lt_of_le_of_ne q.2 (Ne.symm hq0)
          have hne : lpNorm (q : ℝ) x ≠ 0 :=
            (lpNorm_eq_zero_iff hqpos x).not.mpr hx
          have hpos : 0 < lpNorm (q : ℝ) x :=
            lt_of_le_of_ne (lpNorm_nonneg (q : ℝ) x) (Ne.symm hne)
          rw [parameterPowerMean_coeNNReal, if_neg hq0]
          exact hpos

end ConditionalEntropy
