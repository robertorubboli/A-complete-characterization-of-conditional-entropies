import ConditionalEntropy.FiniteSupportMeasures
import ConditionalEntropy.RenyiPowerMean
import ConditionalEntropy.MonomialCalculus
import ConditionalEntropy.PowerMean
import ConditionalEntropy.CurvatureClosure
import ConditionalEntropy.Moments
import ConditionalEntropy.ColumnFunctions
import ConditionalEntropy.Discretization

/-!
# Finite-support sufficiency

This file carries out the finite atomic power-mean factorisation and the
three curvature implications in the finite-support sufficiency proposition.
All endpoint approximations used below are total sequences of probability
measures; no endpoint value is silently fed to the nonendpoint logarithmic
formula.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

/-! ## The finite atomic monomial -/

/-- Exponents in the atomic factorisation.  Coordinate zero is the mass
factor and every successor coordinate is one atomic power mean. -/
def atomicBeta {N : ℕ} (t : ℝ) (alpha : Fin N → Param)
    (w : Fin N → ℝ) : Fin (N + 1) → ℝ :=
  Fin.cases
    (1 - ∑ ell, t * singularWeight (alpha ell) * w ell)
    (fun ell ↦ t * singularWeight (alpha ell) * w ell)

/-- Inner coordinates in the atomic factorisation. -/
def atomicInner {I : Type u} [Fintype I] [Nonempty I] {N : ℕ}
    (alpha : Fin N → Param) (x : ConeVec I) : Fin (N + 1) → ℝ :=
  Fin.cases (l1Mass x.1) (fun ell ↦ parameterPowerMean (alpha ell) x)

theorem atomicBeta_isAffine {N : ℕ} (t : ℝ) (alpha : Fin N → Param)
    (w : Fin N → ℝ) : IsAffineFamily (atomicBeta t alpha w) := by
  unfold IsAffineFamily atomicBeta
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  ring

theorem atomicInner_pos {I : Type u} [Fintype I] [Nonempty I] {N : ℕ}
    (alpha : Fin N → Param) (x : ConeVec I) (hx : x ≠ 0) :
    atomicInner alpha x ∈
      (positiveOrthant : Set (Fin (N + 1) → ℝ)) := by
  intro j
  refine Fin.cases ?_ (fun ell ↦ ?_) j
  · exact (coneNonzeroMass x).mp hx
  · exact parameterPowerCurvature.2.2 (alpha ell) x hx

/-- A convex combination of two nonzero cone vectors is nonzero, including
the two closed-interval endpoints. -/
theorem coneMix_ne_zero_of_both_ne {I : Type u}
    (x z : ConeVec I) (hx : x ≠ 0) (hz : z ≠ 0)
    (lambda : ℝ) (hlambda : lambda ∈ Icc (0 : ℝ) 1) :
    coneMix lambda hlambda x z ≠ 0 := by
  rcases hlambda.1.eq_or_lt with hzero | hpos
  · subst lambda
    simpa [coneMix] using hz
  rcases hlambda.2.eq_or_lt with hone | hlt
  · subst lambda
    simpa [coneMix] using hx
  · intro hmix
    apply (posMix lambda ⟨hpos, hlt⟩ ⟨x, by
      intro h
      exact hx (Subtype.ext h)⟩ ⟨z, by
      intro h
      exact hz (Subtype.ext h)⟩).2
    have hraw := congrArg Subtype.val hmix
    change (fun i ↦ lambda * x.1 i + (1 - lambda) * z.1 i) = 0 at hraw ⊢
    exact hraw

/-- Coordinatewise monotonicity of an affine monomial with nonnegative
exponents. -/
theorem affineMonomial_mono_of_nonnegative {m : ℕ} (beta : Fin m → ℝ)
    (hbeta : ∀ j, 0 ≤ beta j) {a b : Fin m → ℝ}
    (ha : a ∈ (positiveOrthant : Set (Fin m → ℝ)))
    (_hb : b ∈ (positiveOrthant : Set (Fin m → ℝ)))
    (hab : ∀ j, a j ≤ b j) :
    affineMonomial beta a ≤ affineMonomial beta b := by
  unfold affineMonomial
  apply Finset.prod_le_prod
  · intro j _
    exact Real.rpow_nonneg (ha j).le _
  · intro j _
    exact Real.rpow_le_rpow (ha j).le (hab j) (hbeta j)

/-- Mixed coordinate monotonicity for the sign partition used in the convex
composition rule. -/
theorem affineMonomial_mono_of_partition {m : ℕ} (beta : Fin m → ℝ)
    (Ipos Ineg : Finset (Fin m)) (hcover : Ipos ∪ Ineg = Finset.univ)
    (hpos : ∀ j ∈ Ipos, 0 ≤ beta j)
    (hneg : ∀ j ∈ Ineg, beta j ≤ 0)
    {a b : Fin m → ℝ}
    (ha : a ∈ (positiveOrthant : Set (Fin m → ℝ)))
    (hb : b ∈ (positiveOrthant : Set (Fin m → ℝ)))
    (habPos : ∀ j ∈ Ipos, a j ≤ b j)
    (habNeg : ∀ j ∈ Ineg, b j ≤ a j) :
    affineMonomial beta a ≤ affineMonomial beta b := by
  unfold affineMonomial
  apply Finset.prod_le_prod
  · intro j _
    exact Real.rpow_nonneg (ha j).le _
  · intro j hj
    have hjcover : j ∈ Ipos ∨ j ∈ Ineg := by
      have : j ∈ Ipos ∪ Ineg := by rw [hcover]; exact hj
      simpa only [Finset.mem_union] using this
    rcases hjcover with hjpos | hjneg
    · exact Real.rpow_le_rpow (ha j).le (habPos j hjpos) (hpos j hjpos)
    · exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (hneg j hjneg)
        (hb j) (ha j) (habNeg j hjneg)

/-- Exact finite atomic factorisation on the punctured cone. -/
theorem columnPhi_eq_atomicMonomial {I : Type u} [Fintype I] [Nonempty I]
    (tau : ProbabilityMeasure Param) (t : ℝ) {N : ℕ}
    (alpha : Fin N → Param) (w : Fin N → ℝ)
    (hatomic : ∀ p : ProbVec I,
      integratedEntropyPos (probMeasure tau) p =
        ∑ ell, w ell * renyi (alpha ell) p)
    (halpha0 : ∀ ell, alpha ell ≠ 0)
    (halpha1 : ∀ ell, alpha ell ≠ 1)
    (x : ConeVec I) (hx : x ≠ 0) :
    columnPhi t tau x =
      affineMonomial (atomicBeta t alpha w) (atomicInner alpha x) := by
  let mass := l1Mass x.1
  have hmass : 0 < mass := by
    simpa only [mass] using (coneNonzeroMass x).mp hx
  have hmean : ∀ ell, 0 < parameterPowerMean (alpha ell) x :=
    fun ell ↦ parameterPowerCurvature.2.2 (alpha ell) x hx
  have hrenyi : ∀ ell,
      renyi (alpha ell) (normalize (toPosCone x hx)) =
        singularWeight (alpha ell) *
          (Real.log (parameterPowerMean (alpha ell) x) - Real.log mass) := by
    intro ell
    simpa only [mass] using
      renyiNormFormula (alpha ell) (halpha0 ell) (halpha1 ell) x hx
  rw [columnPhi_of_ne t tau x hx, hatomic]
  unfold affineMonomial atomicBeta atomicInner
  rw [Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [Real.rpow_def_of_pos hmass]
  simp_rw [Real.rpow_def_of_pos (hmean _)]
  rw [← Real.exp_sum]
  change mass * Real.exp _ = _
  conv_lhs =>
    rw [show mass = Real.exp (Real.log mass) from (Real.exp_log hmass).symm]
    rw [← Real.exp_add]
  rw [← Real.exp_add]
  congr 1
  simp_rw [hrenyi]
  rw [Finset.mul_sum]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hmassSum :
      (∑ ell, t * (w ell * (singularWeight (alpha ell) * Real.log mass))) =
        Real.log mass * ∑ ell, t * singularWeight (alpha ell) * w ell := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ell _
    ring
  have hmeanSum :
      (∑ ell, t * (w ell *
        (singularWeight (alpha ell) *
          Real.log (parameterPowerMean (alpha ell) x)))) =
        ∑ ell, t * Real.log (parameterPowerMean (alpha ell) x) *
          singularWeight (alpha ell) * w ell := by
    apply Finset.sum_congr rfl
    intro ell _
    ring
  rw [hmassSum, hmeanSum]
  ring_nf

/-! ## Exact atomic moments -/

theorem toReal_omegaLower_of_Ioo {a : Param}
    (ha : a ∈ Ioo (0 : Param) 1) :
    ENNReal.toReal (omegaLower a) = singularWeight a := by
  unfold omegaLower
  rw [if_pos ⟨ha.1.le, ha.2⟩, ENNReal.toReal_ofReal]
  exact (singularWeight_pos_of_Ioo ha).le

theorem omegaUpper_of_le_one {a : Param} (ha : a ≤ 1) : omegaUpper a = 0 := by
  unfold omegaUpper
  rw [if_neg]
  simpa only [mem_Ioi] using (not_lt_of_ge ha)

theorem omegaLower_of_one_lt {a : Param} (ha : 1 < a) : omegaLower a = 0 := by
  unfold omegaLower
  rw [if_neg]
  exact fun h ↦ (not_lt_of_ge ha.le) h.2

theorem toReal_omegaUpper_of_one_lt {a : Param} (ha : 1 < a) :
    ENNReal.toReal (omegaUpper a) = -singularWeight a := by
  unfold omegaUpper
  rw [if_pos (show a ∈ Ioi (1 : Param) from ha), ENNReal.toReal_ofReal]
  exact neg_nonneg.mpr (singularWeight_neg_of_one_lt ha).le

/-! ## A reusable finite atomic presentation -/

/-- The exact data supplied by finite support, bundled so that the three
parameter regimes use the same atoms and weights. -/
structure AtomicPresentation (tau : ProbabilityMeasure Param) where
  N : ℕ
  hN : 0 < N
  alpha : Fin N → Param
  alpha_injective : Function.Injective alpha
  alpha_range : Set.range alpha = suppMeasure (probMeasure tau)
  m : Fin N → ENNReal
  w : Fin N → ℝ
  m_def : ∀ ell, m ell = probMeasure tau ({alpha ell} : Set Param)
  w_def : ∀ ell, w ell = ENNReal.toReal (m ell)
  m_ne_top : ∀ ell, m ell ≠ ⊤
  m_pos : ∀ ell, 0 < m ell
  w_pos : ∀ ell, 0 < w ell
  w_sum : (∑ ell, w ell) = 1
  measure_eq : probMeasure tau =
    ∑ ell, m ell • diracRaw (alpha ell)
  real_integral : ∀ f : Param → ℝ, Measurable f →
    (∃ C : ℝ, ∀ a, |f a| ≤ C) →
    ∫ a, f a ∂(probMeasure tau) = ∑ ell, w ell * f (alpha ell)
  lintegral : ∀ g : Param → ENNReal, Measurable g →
    ∫⁻ a, g a ∂(probMeasure tau) = ∑ ell, m ell * g (alpha ell)

theorem exists_atomicPresentation (tau : ProbabilityMeasure Param)
    (hfin : (suppMeasure (probMeasure tau)).Finite) :
    Nonempty (AtomicPresentation tau) := by
  obtain ⟨N, hN, alpha, hinj, hrange⟩ := finiteSupportEnumeration tau hfin
  let m : Fin N → ENNReal := fun ell ↦
    probMeasure tau ({alpha ell} : Set Param)
  let w : Fin N → ℝ := fun ell ↦ ENNReal.toReal (m ell)
  obtain ⟨hmTop, hmPos, hwPos, hwSum, hmeasure, hreal, hlin⟩ :=
    finiteSupportDirac N hN alpha hinj tau hrange.symm
  exact ⟨{
    N := N
    hN := hN
    alpha := alpha
    alpha_injective := hinj
    alpha_range := hrange
    m := m
    w := w
    m_def := fun _ ↦ rfl
    w_def := fun _ ↦ rfl
    m_ne_top := hmTop
    m_pos := hmPos
    w_pos := hwPos
    w_sum := hwSum
    measure_eq := hmeasure
    real_integral := hreal
    lintegral := hlin }⟩

theorem AtomicPresentation.alpha_mem_support {tau : ProbabilityMeasure Param}
    (A : AtomicPresentation tau) (ell : Fin A.N) :
    A.alpha ell ∈ suppMeasure (probMeasure tau) := by
  rw [← A.alpha_range]
  exact Set.mem_range_self ell

theorem AtomicPresentation.entropy_eq {I : Type u} [Fintype I] [Nonempty I]
    {tau : ProbabilityMeasure Param} (A : AtomicPresentation tau)
    (p : ProbVec I) :
    integratedEntropyPos (probMeasure tau) p =
      ∑ ell, A.w ell * renyi (A.alpha ell) p := by
  unfold integratedEntropyPos
  apply A.real_integral (fun a ↦ renyi a p) (measurable_renyi p)
  refine ⟨Real.log (Fintype.card I : ℝ), fun a ↦ ?_⟩
  rw [abs_of_nonneg (renyi_nonneg a p)]
  exact renyi_le_log_card a p

theorem AtomicPresentation.MLower_toReal {tau : ProbabilityMeasure Param}
    (A : AtomicPresentation tau) :
    (MLower (probMeasure tau)).toReal =
      ∑ ell, A.w ell * (omegaLower (A.alpha ell)).toReal := by
  unfold MLower
  rw [A.lintegral omegaLower measurable_omegaLower]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro ell _
    rw [ENNReal.toReal_mul, A.w_def]
  · intro ell _
    exact ENNReal.mul_ne_top (A.m_ne_top ell)
      (ne_of_lt (omegaLower_lt_top (A.alpha ell)))

theorem AtomicPresentation.MUpper_toReal {tau : ProbabilityMeasure Param}
    (A : AtomicPresentation tau) :
    (MUpper (probMeasure tau)).toReal =
      ∑ ell, A.w ell * (omegaUpper (A.alpha ell)).toReal := by
  unfold MUpper
  rw [A.lintegral omegaUpper measurable_omegaUpper]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro ell _
    rw [ENNReal.toReal_mul, A.w_def]
  · intro ell _
    exact ENNReal.mul_ne_top (A.m_ne_top ell)
      (ne_of_lt (omegaUpper_lt_top (A.alpha ell)))

theorem AtomicPresentation.MReal_eq {tau : ProbabilityMeasure Param}
    (A : AtomicPresentation tau) :
    MReal (probMeasure tau) =
      ∑ ell, A.w ell *
        ((omegaLower (A.alpha ell)).toReal -
          (omegaUpper (A.alpha ell)).toReal) := by
  unfold MReal
  rw [A.MLower_toReal, A.MUpper_toReal, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ell _
  ring

theorem AtomicPresentation.alpha_ne_of_atom_zero
    {tau : ProbabilityMeasure Param} (A : AtomicPresentation tau)
    {a : Param} (ha : probMeasure tau ({a} : Set Param) = 0)
    (ell : Fin A.N) : A.alpha ell ≠ a := by
  intro h
  have hm := A.m_pos ell
  rw [A.m_def, h, ha] at hm
  exact (lt_irrefl 0) hm

theorem AtomicPresentation.lower_interior
    {tau : ProbabilityMeasure Param} (A : AtomicPresentation tau)
    (hsupp : suppMeasure (probMeasure tau) ⊆ Set.Icc (0 : Param) 1)
    (hzero : probMeasure tau ({0} : Set Param) = 0)
    (hone : probMeasure tau ({1} : Set Param) = 0)
    (ell : Fin A.N) : A.alpha ell ∈ Ioo (0 : Param) 1 := by
  have hclosed := hsupp (A.alpha_mem_support ell)
  exact ⟨lt_of_le_of_ne hclosed.1
      (Ne.symm (A.alpha_ne_of_atom_zero hzero ell)),
    lt_of_le_of_ne hclosed.2 (A.alpha_ne_of_atom_zero hone ell)⟩

theorem AtomicPresentation.lowerMoment_eq_singularSum
    {tau : ProbabilityMeasure Param} (A : AtomicPresentation tau)
    (halpha : ∀ ell, A.alpha ell ∈ Ioo (0 : Param) 1) :
    (MLower (probMeasure tau)).toReal =
      ∑ ell, A.w ell * singularWeight (A.alpha ell) := by
  rw [A.MLower_toReal]
  apply Finset.sum_congr rfl
  intro ell _
  rw [toReal_omegaLower_of_Ioo (halpha ell)]

theorem signedOmega_eq_singularWeight {a : Param}
    (ha : a ∈ Ioo (0 : Param) 1 ∨ 1 < a) :
    (omegaLower a).toReal - (omegaUpper a).toReal = singularWeight a := by
  rcases ha with ha | ha
  · rw [toReal_omegaLower_of_Ioo ha, omegaUpper_of_le_one ha.2.le]
    simp
  · rw [omegaLower_of_one_lt ha, toReal_omegaUpper_of_one_lt ha]
    simp

theorem AtomicPresentation.realMoment_eq_singularSum
    {tau : ProbabilityMeasure Param} (A : AtomicPresentation tau)
    (halpha : ∀ ell, A.alpha ell ∈ Ioo (0 : Param) 1 ∨
      1 < A.alpha ell) :
    MReal (probMeasure tau) =
      ∑ ell, A.w ell * singularWeight (A.alpha ell) := by
  rw [A.MReal_eq]
  apply Finset.sum_congr rfl
  intro ell _
  rw [signedOmega_eq_singularWeight (halpha ell)]

/-! ## Curvature of an exact atomic factorisation -/

/-- The composition argument for the all-nonnegative exponent pattern. -/
theorem atomicFactorization_concave {I : Type u} [Fintype I] [Nonempty I]
    (tau : ProbabilityMeasure Param) (t : ℝ) {N : ℕ}
    (alpha : Fin N → Param) (w : Fin N → ℝ)
    (hatomic : ∀ p : ProbVec I,
      integratedEntropyPos (probMeasure tau) p =
        ∑ ell, w ell * renyi (alpha ell) p)
    (halpha0 : ∀ ell, alpha ell ≠ 0)
    (halpha1 : ∀ ell, alpha ell ≠ 1)
    (hbeta : ∀ j, 0 ≤ atomicBeta t alpha w j)
    (halphaLower : ∀ ell, alpha ell < 1) :
    ConcaveCone (columnPhi (I := I) t tau) := by
  apply (originExtension (columnPhi (I := I) t tau) (columnPhi_zero t tau)
    (columnPhi_posHomOne (I := I) t tau)).1
  intro x z hx hz lambda hlambda
  have hw := coneMix_ne_zero_of_both_ne x z hx hz lambda hlambda
  rw [columnPhi_eq_atomicMonomial tau t alpha w hatomic halpha0 halpha1 x hx,
    columnPhi_eq_atomicMonomial tau t alpha w hatomic halpha0 halpha1 z hz,
    columnPhi_eq_atomicMonomial tau t alpha w hatomic halpha0 halpha1
      (coneMix lambda hlambda x z) hw]
  apply (coneCompositionRule (N + 1) (atomicInner alpha)
    positiveOrthant (affineMonomial (atomicBeta t alpha w))
    positiveOrthant_convex (atomicInner_pos alpha) x z hx hz lambda hlambda hw).1
  refine ⟨(affineMonomial_concaveOn_iff _
    (atomicBeta_isAffine t alpha w)).2 hbeta, ?_, ?_⟩
  · intro a ha b hb hab
    exact affineMonomial_mono_of_nonnegative _ hbeta ha hb hab
  · intro j
    refine Fin.cases ?_ (fun ell ↦ ?_) j
    · exact (l1Mass_concave_convex (I := I)).1 x z lambda hlambda
    · exact (parameterPowerCurvature.1 (alpha ell) (halphaLower ell))
        x z lambda hlambda

/-- The composition argument for the manuscript's unique-positive exponent
pattern. The unique positive coordinate must have a convex inner function;
all remaining coordinates must have concave inner functions. -/
theorem atomicFactorization_convex {I : Type u} [Fintype I] [Nonempty I]
    (tau : ProbabilityMeasure Param) (t : ℝ) {N : ℕ}
    (alpha : Fin N → Param) (w : Fin N → ℝ)
    (hatomic : ∀ p : ProbVec I,
      integratedEntropyPos (probMeasure tau) p =
        ∑ ell, w ell * renyi (alpha ell) p)
    (halpha0 : ∀ ell, alpha ell ≠ 0)
    (halpha1 : ∀ ell, alpha ell ≠ 1)
    (k : Fin (N + 1))
    (hkpos : 0 < atomicBeta t alpha w k)
    (hknonpos : ∀ j, j ≠ k → atomicBeta t alpha w j ≤ 0)
    (hinnerConv : ConvexCone (fun x : ConeVec I ↦ atomicInner alpha x k))
    (hinnerConc : ∀ j, j ≠ k →
      ConcaveCone (fun x : ConeVec I ↦ atomicInner alpha x j)) :
    ConvexCone (columnPhi (I := I) t tau) := by
  apply (originExtension (columnPhi (I := I) t tau) (columnPhi_zero t tau)
    (columnPhi_posHomOne (I := I) t tau)).2
  intro x z hx hz lambda hlambda
  have hw := coneMix_ne_zero_of_both_ne x z hx hz lambda hlambda
  rw [columnPhi_eq_atomicMonomial tau t alpha w hatomic halpha0 halpha1 x hx,
    columnPhi_eq_atomicMonomial tau t alpha w hatomic halpha0 halpha1 z hz,
    columnPhi_eq_atomicMonomial tau t alpha w hatomic halpha0 halpha1
      (coneMix lambda hlambda x z) hw]
  let Ipos : Finset (Fin (N + 1)) := {k}
  let Ineg : Finset (Fin (N + 1)) := Finset.univ.erase k
  apply (coneCompositionRule (N + 1) (atomicInner alpha)
    positiveOrthant (affineMonomial (atomicBeta t alpha w))
    positiveOrthant_convex (atomicInner_pos alpha) x z hx hz lambda hlambda hw).2
      Ipos Ineg
  · simp [Ipos, Ineg]
  · ext j
    by_cases hj : j = k <;> simp [Ipos, Ineg, hj]
  · apply (affineMonomial_convexOn_iff _
      (atomicBeta_isAffine t alpha w)).2
    exact ⟨k, hkpos, hknonpos⟩
  · intro a ha b hb habPos habNeg
    apply affineMonomial_mono_of_partition _ Ipos Ineg
      (by
        ext j
        by_cases hj : j = k <;> simp [Ipos, Ineg, hj])
    · intro j hj
      have hjk : j = k := by simpa [Ipos] using hj
      subst j
      exact hkpos.le
    · intro j hj
      exact hknonpos j (by simpa [Ineg] using hj)
    · exact ha
    · exact hb
    · exact habPos
    · exact habNeg
  · intro j hj
    have hjk : j = k := by simpa [Ipos] using hj
    subst j
    exact hinnerConv x z lambda hlambda
  · intro j hj
    exact (hinnerConc j (by simpa [Ineg] using hj)) x z lambda hlambda

/-! ## The exact no-endpoint finite-support theorem -/

/-- Finite-support sufficiency when neither endpoint carries mass. This is
the exact power-mean/monomial core of the manuscript proof; no continuity or
limiting assertion occurs in this theorem. -/
theorem finiteSufficiency_noEndpoints
    (tau : ProbabilityMeasure Param)
    (hfin : (suppMeasure (probMeasure tau)).Finite)
    (hzero : probMeasure tau ({0} : Set Param) = 0)
    (hone : probMeasure tau ({1} : Set Param) = 0)
    (t : ℝ) (astar : Param)
    {I : Type u} [Fintype I] [Nonempty I] :
    (PosAdm t tau → ConcaveCone (columnPhi (I := I) t tau)) ∧
    (NegLowerAdm t tau → ConvexCone (columnPhi (I := I) t tau)) ∧
    (NegExcAdm t tau astar → ConvexCone (columnPhi (I := I) t tau)) := by
  let A : AtomicPresentation tau := (exists_atomicPresentation tau hfin).some
  constructor
  · rintro ⟨ht, hsupp, _honeAdm, hmoment⟩
    have halpha : ∀ ell, A.alpha ell ∈ Ioo (0 : Param) 1 :=
      A.lower_interior hsupp hzero hone
    let S : ℝ := ∑ ell, A.w ell * singularWeight (A.alpha ell)
    have hmomentEq : (MLower (probMeasure tau)).toReal = S := by
      simpa only [S] using A.lowerMoment_eq_singularSum halpha
    have hrecip : 0 ≤ 1 / t := (one_div_pos.mpr ht).le
    have hmomentReal : (MLower (probMeasure tau)).toReal ≤ 1 / t := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmoment
      simpa only [ENNReal.toReal_ofReal hrecip] using h
    have hSle : S ≤ 1 / t := by rwa [← hmomentEq]
    have hfactor :
        (∑ ell, t * singularWeight (A.alpha ell) * A.w ell) = t * S := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell _
      ring
    have htne : t ≠ 0 := ne_of_gt ht
    have hprod : t * S ≤ 1 := by
      calc
        t * S ≤ t * (1 / t) := mul_le_mul_of_nonneg_left hSle ht.le
        _ = 1 := by field_simp
    have hbeta : ∀ j, 0 ≤ atomicBeta t A.alpha A.w j := by
      intro j
      refine Fin.cases ?_ (fun ell ↦ ?_) j
      · change 0 ≤ 1 - ∑ ell, t * singularWeight (A.alpha ell) * A.w ell
        rw [hfactor]
        exact sub_nonneg.mpr hprod
      · change 0 ≤ t * singularWeight (A.alpha ell) * A.w ell
        exact mul_nonneg
          (mul_nonneg ht.le (singularWeight_pos_of_Ioo (halpha ell)).le)
          (A.w_pos ell).le
    exact atomicFactorization_concave tau t A.alpha A.w
      (fun p ↦ A.entropy_eq p)
      (fun ell ↦ (halpha ell).1.ne')
      (fun ell ↦ (halpha ell).2.ne)
      hbeta (fun ell ↦ (halpha ell).2)
  · constructor
    · rintro ⟨ht, hsupp⟩
      have halpha : ∀ ell, A.alpha ell ∈ Ioo (0 : Param) 1 :=
        A.lower_interior hsupp hzero hone
      let S : ℝ := ∑ ell, A.w ell * singularWeight (A.alpha ell)
      have hSnonneg : 0 ≤ S := by
        dsimp only [S]
        exact Finset.sum_nonneg fun ell _ ↦
          mul_nonneg (A.w_pos ell).le
            (singularWeight_pos_of_Ioo (halpha ell)).le
      have hfactor :
          (∑ ell, t * singularWeight (A.alpha ell) * A.w ell) = t * S := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ell _
        ring
      have hkpos : 0 < atomicBeta t A.alpha A.w (0 : Fin (A.N + 1)) := by
        change 0 < 1 - ∑ ell, t * singularWeight (A.alpha ell) * A.w ell
        rw [hfactor]
        have : t * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ht.le hSnonneg
        linarith
      have hknonpos : ∀ j, j ≠ (0 : Fin (A.N + 1)) →
          atomicBeta t A.alpha A.w j ≤ 0 := by
        intro j hj
        cases j using Fin.cases with
        | zero => exact False.elim (hj rfl)
        | succ ell =>
            change t * singularWeight (A.alpha ell) * A.w ell ≤ 0
            exact (mul_neg_of_neg_of_pos
              (mul_neg_of_neg_of_pos ht
                (singularWeight_pos_of_Ioo (halpha ell)))
              (A.w_pos ell)).le
      apply atomicFactorization_convex tau t A.alpha A.w
        (fun p ↦ A.entropy_eq p)
        (fun ell ↦ (halpha ell).1.ne')
        (fun ell ↦ (halpha ell).2.ne)
        (0 : Fin (A.N + 1)) hkpos hknonpos
      · exact (l1Mass_concave_convex (I := I)).2
      · intro j hj
        cases j using Fin.cases with
        | zero => exact False.elim (hj rfl)
        | succ ell =>
            exact parameterPowerCurvature.1 (A.alpha ell) (halpha ell).2
    · rintro ⟨ht, hastar, hsupp, _honeAdm, _hMLower,
          _hMomFin, hmoment⟩
      have hclass : ∀ ell, A.alpha ell ∈ Ioo (0 : Param) 1 ∨
          A.alpha ell = astar := by
        intro ell
        rcases hsupp (A.alpha_mem_support ell) with hlower | hstar
        · exact Or.inl ⟨lt_of_le_of_ne hlower.1
              (Ne.symm (A.alpha_ne_of_atom_zero hzero ell)),
            lt_of_le_of_ne hlower.2
              (A.alpha_ne_of_atom_zero hone ell)⟩
        · exact Or.inr (Set.mem_singleton_iff.mp hstar)
      have hsignClass : ∀ ell,
          A.alpha ell ∈ Ioo (0 : Param) 1 ∨ 1 < A.alpha ell := by
        intro ell
        rcases hclass ell with hlower | hstar
        · exact Or.inl hlower
        · exact Or.inr (hstar.symm ▸ hastar)
      let S : ℝ := ∑ ell, A.w ell * singularWeight (A.alpha ell)
      have hmomentEq : MReal (probMeasure tau) = S := by
        simpa only [S] using A.realMoment_eq_singularSum hsignClass
      have hSle : S ≤ 1 / t := by rwa [← hmomentEq]
      have hstarExists : ∃ ell, A.alpha ell = astar := by
        by_contra hnone
        push Not at hnone
        have hallLower : ∀ ell, A.alpha ell ∈ Ioo (0 : Param) 1 := by
          intro ell
          rcases hclass ell with hlower | hstar
          · exact hlower
          · exact False.elim (hnone ell hstar)
        have hSnonneg : 0 ≤ S := by
          dsimp only [S]
          exact Finset.sum_nonneg fun ell _ ↦
            mul_nonneg (A.w_pos ell).le
              (singularWeight_pos_of_Ioo (hallLower ell)).le
        have hrecipNeg : 1 / t < 0 := one_div_neg.mpr ht
        linarith
      obtain ⟨ellstar, hellstar⟩ := hstarExists
      have hotherLower : ∀ ell, ell ≠ ellstar →
          A.alpha ell ∈ Ioo (0 : Param) 1 := by
        intro ell hell
        rcases hclass ell with hlower | hstar
        · exact hlower
        · exfalso
          apply hell
          apply A.alpha_injective
          exact hstar.trans hellstar.symm
      have hfactor :
          (∑ ell, t * singularWeight (A.alpha ell) * A.w ell) = t * S := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ell _
        ring
      have htne : t ≠ 0 := ne_of_lt ht
      have hprod : 1 ≤ t * S := by
        calc
          1 = t * (1 / t) := by field_simp
          _ ≤ t * S := mul_le_mul_of_nonpos_left hSle ht.le
      let k : Fin (A.N + 1) := Fin.succ ellstar
      have hkpos : 0 < atomicBeta t A.alpha A.w k := by
        change 0 < t * singularWeight (A.alpha ellstar) * A.w ellstar
        rw [hellstar]
        exact mul_pos
          (mul_pos_of_neg_of_neg ht (singularWeight_neg_of_one_lt hastar))
          (A.w_pos ellstar)
      have hknonpos : ∀ j, j ≠ k →
          atomicBeta t A.alpha A.w j ≤ 0 := by
        intro j hj
        cases j using Fin.cases with
        | zero =>
            change 1 - ∑ ell, t * singularWeight (A.alpha ell) * A.w ell ≤ 0
            rw [hfactor]
            exact sub_nonpos.mpr hprod
        | succ ell =>
          have hell : ell ≠ ellstar := by
            intro heq
            subst ell
            apply hj
            simp only [k]
          change t * singularWeight (A.alpha ell) * A.w ell ≤ 0
          exact (mul_neg_of_neg_of_pos
            (mul_neg_of_neg_of_pos ht
              (singularWeight_pos_of_Ioo (hotherLower ell hell)))
            (A.w_pos ell)).le
      apply atomicFactorization_convex tau t A.alpha A.w
        (fun p ↦ A.entropy_eq p)
        (fun ell ↦ by
          rcases hclass ell with hlower | hstar
          · exact hlower.1.ne'
          · rw [hstar]
            exact ne_of_gt (lt_trans (show (0 : Param) < 1 by simp) hastar))
        (fun ell ↦ by
          rcases hclass ell with hlower | hstar
          · exact hlower.2.ne
          · rw [hstar]
            exact ne_of_gt hastar)
        k hkpos hknonpos
      · change ConvexCone
          (fun x : ConeVec I ↦ parameterPowerMean (A.alpha ellstar) x)
        rw [hellstar]
        exact parameterPowerCurvature.2.1 astar hastar.le
      · intro j hj
        cases j using Fin.cases with
        | zero => exact (l1Mass_concave_convex (I := I)).1
        | succ ell =>
          have hell : ell ≠ ellstar := by
            intro heq
            subst ell
            apply hj
            simp only [k]
          exact parameterPowerCurvature.1 (A.alpha ell)
            (hotherLower ell hell).2

/-! ## Endpoint perturbations and their entropy limits -/

/-- The strictly positive order tending to the Hartley endpoint. -/
def zeroApprox (k : ℕ) : Param :=
  finiteParam (1 / ((k + 2 : ℕ) : ℝ))

theorem zeroApprox_real_pos (k : ℕ) :
    0 < 1 / ((k + 2 : ℕ) : ℝ) := by positivity

theorem zeroApprox_pos (k : ℕ) : 0 < zeroApprox k := by
  exact ENNReal.ofReal_pos.mpr (zeroApprox_real_pos k)

theorem zeroApprox_lt_one (k : ℕ) : zeroApprox k < (1 : Param) := by
  apply ENNReal.ofReal_lt_one.mpr
  have hd : 0 < ((k + 2 : ℕ) : ℝ) := by positivity
  apply (div_lt_iff₀ hd).2
  simpa only [one_mul] using
    (show (1 : ℝ) < (k + 2 : ℕ) by
      exact_mod_cast (show 1 < k + 2 by omega))

theorem zeroApprox_singularWeight (k : ℕ) :
    singularWeight (zeroApprox k) = 1 / ((k + 1 : ℕ) : ℝ) := by
  have hpos := zeroApprox_real_pos k
  have hne : 1 / ((k + 2 : ℕ) : ℝ) ≠ 1 :=
    ne_of_lt (by
      have hd : 0 < ((k + 2 : ℕ) : ℝ) := by positivity
      apply (div_lt_iff₀ hd).2
      simpa only [one_mul] using
        (show (1 : ℝ) < (k + 2 : ℕ) by
          exact_mod_cast (show 1 < k + 2 by omega)))
  rw [zeroApprox, singularWeight_finite hpos.le hne]
  let d : ℝ := (k + 2 : ℕ)
  have hd : d ≠ 0 := by dsimp only [d]; positivity
  have hd1 : d - 1 ≠ 0 := by
    apply ne_of_gt
    apply sub_pos.mpr
    dsimp only [d]
    exact_mod_cast (show 1 < k + 2 by omega)
  have hid : (1 / d) / (1 - 1 / d) = 1 / (d - 1) := by
    field_simp [hd, hd1]
  change (1 / d) / (1 - 1 / d) = _
  rw [hid]
  congr 2
  dsimp only [d]
  push_cast
  ring

theorem tendsto_zeroApprox_real :
    Tendsto (fun k : ℕ ↦ 1 / ((k + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hden : Tendsto (fun k : ℕ ↦ ((k + 2 : ℕ) : ℝ)) atTop atTop := by
    change Tendsto (Nat.cast ∘ fun k : ℕ ↦ k + 2) atTop atTop
    exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2)
  have h := tendsto_inv_atTop_zero.comp hden
  refine h.congr' (Filter.Eventually.of_forall fun k ↦ ?_)
  simp only [Function.comp_apply, one_div]

theorem tendsto_zeroApprox : Tendsto zeroApprox atTop (𝓝 (0 : Param)) := by
  unfold zeroApprox finiteParam
  change Tendsto (fun k : ℕ ↦ ENNReal.ofReal (1 / ((k + 2 : ℕ) : ℝ)))
    atTop (𝓝 (0 : WithTop NNReal))
  have h := ENNReal.tendsto_ofReal tendsto_zeroApprox_real
  dsimp only [ENNReal] at h ⊢
  rw [ENNReal.ofReal_zero] at h
  refine h.congr' (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- Rényi entropy is right-continuous at order zero along `zeroApprox`.
This endpoint statement is proved directly from the finite power sum. -/
theorem tendsto_renyi_zeroApprox
    {J : Type*} [Fintype J] [Nonempty J] (p : ProbVec J) :
    Tendsto (fun k : ℕ ↦ renyi (zeroApprox k) p) atTop
      (𝓝 (renyi (0 : Param) p)) := by
  let r : ℕ → ℝ := fun k ↦ 1 / ((k + 2 : ℕ) : ℝ)
  have hr : Tendsto r atTop (𝓝 0) := tendsto_zeroApprox_real
  have hrpos : ∀ k, 0 < r k := zeroApprox_real_pos
  have hrone : ∀ k, r k ≠ 1 := fun k ↦ ne_of_lt (by
    have hd : 0 < ((k + 2 : ℕ) : ℝ) := by positivity
    apply (div_lt_iff₀ hd).2
    simpa only [one_mul] using
      (show (1 : ℝ) < (k + 2 : ℕ) by
        exact_mod_cast (show 1 < k + 2 by omega)))
  have hcoord : ∀ i : J,
      Tendsto (fun k ↦ p.1 i ^ r k) atTop
        (𝓝 (if p.1 i = 0 then 0 else 1)) := by
    intro i
    by_cases hi : p.1 i = 0
    · have hconst : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds
      simpa only [hi, if_pos, Real.zero_rpow (hrpos _).ne'] using hconst
    · rw [if_neg hi]
      have hpow := (Real.continuousAt_const_rpow (b := 0) hi).tendsto.comp hr
      change Tendsto ((fun x : ℝ ↦ p.1 i ^ x) ∘ r) atTop (𝓝 1)
      simpa only [Real.rpow_zero] using hpow
  have hsum : Tendsto (fun k ↦ powerSum (r k) p) atTop
      (𝓝 ((supportFinset p.1).card : ℝ)) := by
    have h := tendsto_finsetSum Finset.univ fun i _ ↦ hcoord i
    have hval :
        (∑ i : J, if p.1 i = 0 then (0 : ℝ) else 1) =
          ((supportFinset p.1).card : ℝ) := by
      calc
        (∑ i : J, if p.1 i = 0 then (0 : ℝ) else 1) =
            ∑ i : J, if p.1 i ≠ 0 then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro i _
              by_cases hi : p.1 i = 0 <;> simp [hi]
        _ = ((supportFinset p.1).card : ℝ) := by
          simp only [supportFinset, Finset.sum_boole]
    convert h using 1
    · rfl
    · exact congrArg 𝓝 hval.symm
  have hcardPos : 0 < ((supportFinset p.1).card : ℝ) := by
    exact_mod_cast supportFinset_card_pos p
  have hlog : Tendsto (fun k ↦ Real.log (powerSum (r k) p)) atTop
      (𝓝 (Real.log ((supportFinset p.1).card : ℝ))) :=
    (Real.continuousAt_log hcardPos.ne').tendsto.comp hsum
  have hden : Tendsto (fun k ↦ 1 - r k) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hr
  have hfinite : Tendsto (fun k ↦ renyiFinite (r k) p) atTop
      (𝓝 (renyiZero p)) := by
    have hquot := hlog.div hden (by norm_num : (1 : ℝ) ≠ 0)
    have hquot' : Tendsto
        (fun k ↦ Real.log (powerSum (r k) p) / (1 - r k)) atTop
        (𝓝 (Real.log ((supportFinset p.1).card : ℝ) / 1)) :=
      hquot.congr' (Filter.Eventually.of_forall fun _ ↦ rfl)
    simpa only [renyiFinite, renyiZero, div_one] using hquot'
  rw [renyi_at_zero]
  refine hfinite.congr' (Filter.Eventually.of_forall fun k ↦ ?_)
  exact (renyi_finite (hrpos k).le (hrpos k).ne' (hrone k) p).symm

/-- Rényi entropy is left-continuous at the Shannon endpoint along the
standard strictly-lower approximation. -/
theorem tendsto_renyi_shannonApprox_public
    {J : Type*} [Fintype J] [Nonempty J] (p : ProbVec J) :
    Tendsto (fun k : ℕ ↦ renyi (shannonApprox k) p) atTop
      (𝓝 (renyi (1 : Param) p)) := by
  have hreal : Tendsto (fun k : ℕ ↦ ENNReal.toReal (shannonApprox k)) atTop
      (𝓝 (1 : ℝ)) := by
    have h := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp
      tendsto_shannonApprox
    change Tendsto (ENNReal.toReal ∘ shannonApprox) atTop (𝓝 (1 : ℝ))
    simpa only [ENNReal.toReal_one] using h
  have hwithin : Tendsto
      (fun k : ℕ ↦ ENNReal.toReal (shannonApprox k)) atTop
      (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hreal, Filter.Eventually.of_forall fun k ↦ ?_⟩
    have htop : shannonApprox k ≠ (⊤ : Param) := ne_top_of_lt (shannonApprox_lt_one k)
    simpa using (ENNReal.toReal_lt_toReal htop ENNReal.one_ne_top).mpr
      (shannonApprox_lt_one k)
  have hfinite := (tendsto_renyiFinite_nhdsLT_one p).comp hwithin
  rw [renyi_at_one]
  refine hfinite.congr' (Filter.Eventually.of_forall fun k ↦ ?_)
  have htop : shannonApprox k ≠ (⊤ : Param) := ne_top_of_lt (shannonApprox_lt_one k)
  have hzero : shannonApprox k ≠ (0 : Param) := (shannonApprox_pos k).ne'
  have hone : shannonApprox k ≠ (1 : Param) := ne_of_lt (shannonApprox_lt_one k)
  simp [renyi, htop, hzero, hone, paramToReal]

/-- Move only the Hartley endpoint into the open lower interval. -/
def perturbZero (k : ℕ) (a : Param) : Param :=
  if a = 0 then zeroApprox k else a

/-- Move both finite lower endpoints into the open lower interval. -/
def perturbBoth (k : ℕ) (a : Param) : Param :=
  if a = 0 then zeroApprox k else if a = 1 then shannonApprox k else a

theorem measurable_perturbZero (k : ℕ) : Measurable (perturbZero k) := by
  exact Measurable.ite (measurableSet_singleton (0 : Param))
    measurable_const measurable_id

theorem measurable_perturbBoth (k : ℕ) : Measurable (perturbBoth k) := by
  exact Measurable.ite (measurableSet_singleton (0 : Param)) measurable_const
    (Measurable.ite (measurableSet_singleton (1 : Param))
      measurable_const measurable_id)

def perturbZeroProb (tau : ProbabilityMeasure Param) (k : ℕ) :
    ProbabilityMeasure Param :=
  probMap tau (perturbZero k) (measurable_perturbZero k).aemeasurable

def perturbBothProb (tau : ProbabilityMeasure Param) (k : ℕ) :
    ProbabilityMeasure Param :=
  probMap tau (perturbBoth k) (measurable_perturbBoth k).aemeasurable

theorem AtomicPresentation.perturbZero_entropy_eq
    {J : Type*} [Fintype J] [Nonempty J]
    {tau : ProbabilityMeasure Param} (A : AtomicPresentation tau)
    (k : ℕ) (p : ProbVec J) :
    integratedEntropyPos (probMeasure (perturbZeroProb tau k)) p =
      ∑ ell, A.w ell * renyi (perturbZero k (A.alpha ell)) p := by
  unfold integratedEntropyPos perturbZeroProb probMeasure probMap
  change ∫ a, renyi a p ∂(Measure.map (perturbZero k) (probMeasure tau)) = _
  rw [integral_map (measurable_perturbZero k).aemeasurable
    (measurable_renyi p).aestronglyMeasurable]
  apply A.real_integral _ ((measurable_renyi p).comp
    (measurable_perturbZero k))
  refine ⟨Real.log (Fintype.card J : ℝ), fun a ↦ ?_⟩
  change |renyi (perturbZero k a) p| ≤ Real.log (Fintype.card J : ℝ)
  rw [abs_of_nonneg (renyi_nonneg _ p)]
  exact renyi_le_log_card _ p

theorem AtomicPresentation.perturbBoth_entropy_eq
    {J : Type*} [Fintype J] [Nonempty J]
    {tau : ProbabilityMeasure Param} (A : AtomicPresentation tau)
    (k : ℕ) (p : ProbVec J) :
    integratedEntropyPos (probMeasure (perturbBothProb tau k)) p =
      ∑ ell, A.w ell * renyi (perturbBoth k (A.alpha ell)) p := by
  unfold integratedEntropyPos perturbBothProb probMeasure probMap
  change ∫ a, renyi a p ∂(Measure.map (perturbBoth k) (probMeasure tau)) = _
  rw [integral_map (measurable_perturbBoth k).aemeasurable
    (measurable_renyi p).aestronglyMeasurable]
  apply A.real_integral _ ((measurable_renyi p).comp
    (measurable_perturbBoth k))
  refine ⟨Real.log (Fintype.card J : ℝ), fun a ↦ ?_⟩
  change |renyi (perturbBoth k a) p| ≤ Real.log (Fintype.card J : ℝ)
  rw [abs_of_nonneg (renyi_nonneg _ p)]
  exact renyi_le_log_card _ p

/-- A generic finite-atomic limit rule for the column perspective. -/
theorem AtomicPresentation.tendsto_columnPhi_atomic
    {I : Type u} [Fintype I] [Nonempty I]
    {tau : ProbabilityMeasure Param} (A : AtomicPresentation tau)
    (tauN : ℕ → ProbabilityMeasure Param) (tN : ℕ → ℝ)
    (alphaN : ℕ → Fin A.N → Param)
    (hatomic : ∀ n (p : ProbVec I),
      integratedEntropyPos (probMeasure (tauN n)) p =
        ∑ ell, A.w ell * renyi (alphaN n ell) p)
    (ht : Tendsto tN atTop (𝓝 t))
    (halpha : ∀ (p : ProbVec I) ell,
      Tendsto (fun n ↦ renyi (alphaN n ell) p) atTop
        (𝓝 (renyi (A.alpha ell) p))) :
    ∀ x : ConeVec I,
      Tendsto (fun n ↦ columnPhi (tN n) (tauN n) x) atTop
        (𝓝 (columnPhi t tau x)) := by
  intro x
  by_cases hx : x = 0
  · subst x
    simpa only [columnPhi_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  · let p : ProbVec I := normalize (toPosCone x hx)
    have hsum : Tendsto
        (fun n ↦ ∑ ell, A.w ell * renyi (alphaN n ell) p) atTop
        (𝓝 (∑ ell, A.w ell * renyi (A.alpha ell) p)) := by
      exact tendsto_finsetSum Finset.univ fun ell _ ↦
        tendsto_const_nhds.mul (halpha p ell)
    have hent : Tendsto
        (fun n ↦ integratedEntropyPos (probMeasure (tauN n)) p) atTop
        (𝓝 (integratedEntropyPos (probMeasure tau) p)) := by
      rw [A.entropy_eq p]
      exact hsum.congr' (Filter.Eventually.of_forall fun n ↦ (hatomic n p).symm)
    simp_rw [columnPhi_of_ne _ _ x hx]
    exact tendsto_const_nhds.mul
      ((Real.continuous_exp.continuousAt).tendsto.comp (ht.mul hent))

/-! ## Endpoint bookkeeping -/

theorem toReal_omegaLower_of_Icc {a : Param}
    (ha : a ∈ Icc (0 : Param) 1) :
    (omegaLower a).toReal = singularWeight a := by
  rcases ha.1.eq_or_lt with hzero | hpos
  · have : a = 0 := hzero.symm
    subst a
    simp
  · rcases ha.2.lt_or_eq with hone | hone
    · exact toReal_omegaLower_of_Ioo ⟨hpos, hone⟩
    · subst a
      simp

theorem signedOmega_eq_singularWeight_of_closed_or_upper {a astar : Param}
    (hastar : 1 < astar) (ha : a ∈ Icc (0 : Param) 1 ∨ a = astar) :
    (omegaLower a).toReal - (omegaUpper a).toReal = singularWeight a := by
  rcases ha with hlower | hstar
  · rw [toReal_omegaLower_of_Icc hlower, omegaUpper_of_le_one hlower.2]
    simp
  · subst a
    exact signedOmega_eq_singularWeight (Or.inr hastar)

theorem perturbZero_ne_zero (k : ℕ) (a : Param) : perturbZero k a ≠ 0 := by
  by_cases ha : a = 0
  · simp [perturbZero, ha, (zeroApprox_pos k).ne']
  · simp [perturbZero, ha]

theorem perturbZero_ne_one (k : ℕ) {a : Param} (ha : a ≠ 1) :
    perturbZero k a ≠ 1 := by
  by_cases hzero : a = 0
  · simp [perturbZero, hzero, (zeroApprox_lt_one k).ne]
  · simp [perturbZero, hzero, ha]

theorem perturbBoth_ne_zero (k : ℕ) (a : Param) : perturbBoth k a ≠ 0 := by
  by_cases hzero : a = 0
  · simp [perturbBoth, hzero, (zeroApprox_pos k).ne']
  · by_cases hone : a = 1
    · simp [perturbBoth, hone, (shannonApprox_pos k).ne']
    · simp [perturbBoth, hzero, hone]

theorem perturbBoth_ne_one (k : ℕ) (a : Param) : perturbBoth k a ≠ 1 := by
  by_cases hzero : a = 0
  · simp [perturbBoth, hzero, (zeroApprox_lt_one k).ne]
  · by_cases hone : a = 1
    · simp [perturbBoth, hone, (shannonApprox_lt_one k).ne]
    · simp [perturbBoth, hzero, hone]

theorem perturbZero_Ioo {k : ℕ} {a : Param}
    (ha : a ∈ Icc (0 : Param) 1) (ha1 : a ≠ 1) :
    perturbZero k a ∈ Ioo (0 : Param) 1 := by
  by_cases hzero : a = 0
  · subst a
    simp only [perturbZero, if_pos]
    exact ⟨zeroApprox_pos k, zeroApprox_lt_one k⟩
  · rw [perturbZero, if_neg hzero]
    exact ⟨lt_of_le_of_ne ha.1 (Ne.symm hzero),
      lt_of_le_of_ne ha.2 ha1⟩

theorem perturbBoth_Ioo {k : ℕ} {a : Param}
    (ha : a ∈ Icc (0 : Param) 1) :
    perturbBoth k a ∈ Ioo (0 : Param) 1 := by
  by_cases hzero : a = 0
  · subst a
    simp only [perturbBoth, if_pos]
    exact ⟨zeroApprox_pos k, zeroApprox_lt_one k⟩
  · by_cases hone : a = 1
    · subst a
      simp only [perturbBoth, if_neg (show (1 : Param) ≠ 0 by simp), if_pos]
      exact ⟨shannonApprox_pos k, shannonApprox_lt_one k⟩
    · rw [perturbBoth, if_neg hzero, if_neg hone]
      exact ⟨lt_of_le_of_ne ha.1 (Ne.symm hzero),
        lt_of_le_of_ne ha.2 hone⟩

theorem tendsto_renyi_perturbZero
    {J : Type*} [Fintype J] [Nonempty J]
    (p : ProbVec J) (a : Param) :
    Tendsto (fun k : ℕ ↦ renyi (perturbZero k a) p) atTop
      (𝓝 (renyi a p)) := by
  by_cases hzero : a = 0
  · subst a
    simpa only [perturbZero, if_pos] using tendsto_renyi_zeroApprox p
  · simpa only [perturbZero, if_neg hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ renyi a p) atTop
        (𝓝 (renyi a p)))

theorem tendsto_renyi_perturbBoth
    {J : Type*} [Fintype J] [Nonempty J]
    (p : ProbVec J) (a : Param) :
    Tendsto (fun k : ℕ ↦ renyi (perturbBoth k a) p) atTop
      (𝓝 (renyi a p)) := by
  by_cases hzero : a = 0
  · subst a
    simpa only [perturbBoth, if_pos] using tendsto_renyi_zeroApprox p
  · by_cases hone : a = 1
    · subst a
      simpa only [perturbBoth, if_neg (show (1 : Param) ≠ 0 by simp), if_pos]
        using tendsto_renyi_shannonApprox_public p
    · simpa only [perturbBoth, if_neg hzero, if_neg hone] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ renyi a p) atTop
          (𝓝 (renyi a p)))

theorem tendsto_singularWeight_perturbZero (a : Param) :
    Tendsto (fun k : ℕ ↦ singularWeight (perturbZero k a)) atTop
      (𝓝 (singularWeight a)) := by
  by_cases hzero : a = 0
  · subst a
    simp only [perturbZero, if_pos, singularWeight_zero,
      zeroApprox_singularWeight]
    have hden : Tendsto (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ)) atTop atTop := by
      change Tendsto (Nat.cast ∘ fun k : ℕ ↦ k + 1) atTop atTop
      exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp
        (tendsto_add_atTop_nat 1)
    have h := tendsto_inv_atTop_zero.comp hden
    refine h.congr' (Filter.Eventually.of_forall fun k ↦ ?_)
    simp only [Function.comp_apply, one_div]
  · simpa only [perturbZero, if_neg hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ singularWeight a) atTop
        (𝓝 (singularWeight a)))

/-! ## The three endpoint-closed branches -/

theorem finiteSufficiency_positive
    (tau : ProbabilityMeasure Param)
    (hfin : (suppMeasure (probMeasure tau)).Finite)
    (t : ℝ) {I : Type u} [Fintype I] [Nonempty I]
    (hAdm : PosAdm t tau) :
    ConcaveCone (columnPhi (I := I) t tau) := by
  rcases hAdm with ⟨ht, hsupp, hone, hmoment⟩
  let A : AtomicPresentation tau := (exists_atomicPresentation tau hfin).some
  have hclosed : ∀ ell, A.alpha ell ∈ Icc (0 : Param) 1 :=
    fun ell ↦ hsupp (A.alpha_mem_support ell)
  have halphaOne : ∀ ell, A.alpha ell ≠ 1 :=
    A.alpha_ne_of_atom_zero hone
  let alphaN : ℕ → Fin A.N → Param :=
    fun n ell ↦ perturbZero n (A.alpha ell)
  let tauN : ℕ → ProbabilityMeasure Param :=
    fun n ↦ perturbZeroProb tau n
  let S : ℝ := ∑ ell, A.w ell * singularWeight (A.alpha ell)
  let Sn : ℕ → ℝ := fun n ↦
    ∑ ell, A.w ell * singularWeight (alphaN n ell)
  let D : ℕ → ℝ := fun n ↦ Sn n - S
  let tN : ℕ → ℝ := fun n ↦ t / (1 + t * D n)
  have hmomentEq : (MLower (probMeasure tau)).toReal = S := by
    rw [A.MLower_toReal]
    dsimp only [S]
    apply Finset.sum_congr rfl
    intro ell _
    rw [toReal_omegaLower_of_Icc (hclosed ell)]
  have hrecip : 0 ≤ 1 / t := (one_div_pos.mpr ht).le
  have hmomentReal : (MLower (probMeasure tau)).toReal ≤ 1 / t := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmoment
    simpa only [ENNReal.toReal_ofReal hrecip] using h
  have hSle : S ≤ 1 / t := by rwa [← hmomentEq]
  have hbase : t * S ≤ 1 := by
    calc
      t * S ≤ t * (1 / t) := mul_le_mul_of_nonneg_left hSle ht.le
      _ = 1 := by field_simp
  have hDnonneg : ∀ n, 0 ≤ D n := by
    intro n
    apply sub_nonneg.mpr
    dsimp only [D, Sn, S, alphaN]
    apply Finset.sum_le_sum
    intro ell _
    apply mul_le_mul_of_nonneg_left _ (A.w_pos ell).le
    by_cases hzero : A.alpha ell = 0
    · rw [hzero]
      simp only [perturbZero, if_pos, singularWeight_zero]
      exact (singularWeight_pos_of_Ioo
        ⟨zeroApprox_pos n, zeroApprox_lt_one n⟩).le
    · rw [perturbZero, if_neg hzero]
  have hSn : Tendsto Sn atTop (𝓝 S) := by
    dsimp only [Sn, S, alphaN]
    exact tendsto_finsetSum Finset.univ fun ell _ ↦
      tendsto_const_nhds.mul
        (tendsto_singularWeight_perturbZero (A.alpha ell))
  have hD : Tendsto D atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ S) atTop (𝓝 S) := tendsto_const_nhds
    simpa only [D, sub_self] using hSn.sub hconst
  have htN : Tendsto tN atTop (𝓝 t) := by
    have hden : Tendsto (fun n ↦ 1 + t * D n) atTop (𝓝 1) := by
      simpa only [mul_zero, add_zero] using
        tendsto_const_nhds.add (tendsto_const_nhds.mul hD)
    have hnum : Tendsto (fun _ : ℕ ↦ t) atTop (𝓝 t) := tendsto_const_nhds
    have hquot := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
    dsimp only [tN]
    rw [div_one] at hquot
    refine hquot.congr' (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hdenPos : ∀ n, 0 < 1 + t * D n := fun n ↦
    lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right
      (mul_nonneg ht.le (hDnonneg n)))
  have htNpos : ∀ n, 0 < tN n := fun n ↦
    div_pos ht (hdenPos n)
  have hinterior : ∀ n ell, alphaN n ell ∈ Ioo (0 : Param) 1 :=
    fun n ell ↦ perturbZero_Ioo (hclosed ell) (halphaOne ell)
  have hatomic : ∀ n (p : ProbVec I),
      integratedEntropyPos (probMeasure (tauN n)) p =
        ∑ ell, A.w ell * renyi (alphaN n ell) p := by
    intro n p
    exact A.perturbZero_entropy_eq n p
  have hcurv : ∀ n, ConcaveCone (columnPhi (I := I) (tN n) (tauN n)) := by
    intro n
    have hfactor :
        (∑ ell, tN n * singularWeight (alphaN n ell) * A.w ell) =
          tN n * Sn n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell _
      ring
    have hprod : tN n * Sn n ≤ 1 := by
      change t / (1 + t * D n) * Sn n ≤ 1
      rw [div_mul_eq_mul_div]
      apply (div_le_one (hdenPos n)).2
      dsimp only [D]
      nlinarith
    have hbeta : ∀ j, 0 ≤ atomicBeta (tN n) (alphaN n) A.w j := by
      intro j
      refine Fin.cases ?_ (fun ell ↦ ?_) j
      · change 0 ≤ 1 -
          ∑ ell, tN n * singularWeight (alphaN n ell) * A.w ell
        rw [hfactor]
        exact sub_nonneg.mpr hprod
      · change 0 ≤ tN n * singularWeight (alphaN n ell) * A.w ell
        exact mul_nonneg
          (mul_nonneg (htNpos n).le
            (singularWeight_pos_of_Ioo (hinterior n ell)).le)
          (A.w_pos ell).le
    exact atomicFactorization_concave (tauN n) (tN n) (alphaN n) A.w
      (hatomic n)
      (fun ell ↦ (hinterior n ell).1.ne')
      (fun ell ↦ (hinterior n ell).2.ne)
      hbeta (fun ell ↦ (hinterior n ell).2)
  apply (pointwiseCurvatureLimit
    (fun n ↦ columnPhi (I := I) (tN n) (tauN n))
    (columnPhi (I := I) t tau) ?_).1 hcurv
  apply A.tendsto_columnPhi_atomic tauN tN alphaN hatomic htN
  intro p ell
  exact tendsto_renyi_perturbZero p (A.alpha ell)

theorem finiteSufficiency_negativeLower
    (tau : ProbabilityMeasure Param)
    (hfin : (suppMeasure (probMeasure tau)).Finite)
    (t : ℝ) {I : Type u} [Fintype I] [Nonempty I]
    (hAdm : NegLowerAdm t tau) :
    ConvexCone (columnPhi (I := I) t tau) := by
  rcases hAdm with ⟨ht, hsupp⟩
  let A : AtomicPresentation tau := (exists_atomicPresentation tau hfin).some
  have hclosed : ∀ ell, A.alpha ell ∈ Icc (0 : Param) 1 :=
    fun ell ↦ hsupp (A.alpha_mem_support ell)
  let alphaN : ℕ → Fin A.N → Param :=
    fun n ell ↦ perturbBoth n (A.alpha ell)
  let tauN : ℕ → ProbabilityMeasure Param :=
    fun n ↦ perturbBothProb tau n
  have hinterior : ∀ n ell, alphaN n ell ∈ Ioo (0 : Param) 1 :=
    fun n ell ↦ perturbBoth_Ioo (hclosed ell)
  have hatomic : ∀ n (p : ProbVec I),
      integratedEntropyPos (probMeasure (tauN n)) p =
        ∑ ell, A.w ell * renyi (alphaN n ell) p := by
    intro n p
    exact A.perturbBoth_entropy_eq n p
  have hcurv : ∀ n, ConvexCone (columnPhi (I := I) t (tauN n)) := by
    intro n
    let Sn : ℝ := ∑ ell, A.w ell * singularWeight (alphaN n ell)
    have hSn : 0 ≤ Sn := by
      dsimp only [Sn]
      exact Finset.sum_nonneg fun ell _ ↦
        mul_nonneg (A.w_pos ell).le
          (singularWeight_pos_of_Ioo (hinterior n ell)).le
    have hfactor :
        (∑ ell, t * singularWeight (alphaN n ell) * A.w ell) =
          t * Sn := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell _
      ring
    have hkpos : 0 < atomicBeta t (alphaN n) A.w
        (0 : Fin (A.N + 1)) := by
      change 0 < 1 -
        ∑ ell, t * singularWeight (alphaN n ell) * A.w ell
      rw [hfactor]
      have : t * Sn ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ht.le hSn
      linarith
    have hknonpos : ∀ j, j ≠ (0 : Fin (A.N + 1)) →
        atomicBeta t (alphaN n) A.w j ≤ 0 := by
      intro j hj
      cases j using Fin.cases with
      | zero => exact False.elim (hj rfl)
      | succ ell =>
          change t * singularWeight (alphaN n ell) * A.w ell ≤ 0
          exact (mul_neg_of_neg_of_pos
            (mul_neg_of_neg_of_pos ht
              (singularWeight_pos_of_Ioo (hinterior n ell)))
            (A.w_pos ell)).le
    apply atomicFactorization_convex (tauN n) t (alphaN n) A.w
      (hatomic n)
      (fun ell ↦ (hinterior n ell).1.ne')
      (fun ell ↦ (hinterior n ell).2.ne)
      (0 : Fin (A.N + 1)) hkpos hknonpos
    · exact (l1Mass_concave_convex (I := I)).2
    · intro j hj
      cases j using Fin.cases with
      | zero => exact False.elim (hj rfl)
      | succ ell =>
          exact parameterPowerCurvature.1 (alphaN n ell)
            (hinterior n ell).2
  apply (pointwiseCurvatureLimit
    (fun n ↦ columnPhi (I := I) t (tauN n))
    (columnPhi (I := I) t tau) ?_).2 hcurv
  apply A.tendsto_columnPhi_atomic tauN (fun _ ↦ t) alphaN hatomic
    tendsto_const_nhds
  intro p ell
  exact tendsto_renyi_perturbBoth p (A.alpha ell)

theorem finiteSufficiency_negativeExceptional
    (tau : ProbabilityMeasure Param)
    (hfin : (suppMeasure (probMeasure tau)).Finite)
    (t : ℝ) (astar : Param)
    {I : Type u} [Fintype I] [Nonempty I]
    (hAdm : NegExcAdm t tau astar) :
    ConvexCone (columnPhi (I := I) t tau) := by
  rcases hAdm with ⟨ht, hastar, hsupp, hone, _hMLower,
    _hMomFin, hmoment⟩
  let A : AtomicPresentation tau := (exists_atomicPresentation tau hfin).some
  have hclass : ∀ ell, A.alpha ell ∈ Icc (0 : Param) 1 ∨
      A.alpha ell = astar := fun ell ↦ hsupp (A.alpha_mem_support ell)
  have halphaOne : ∀ ell, A.alpha ell ≠ 1 :=
    A.alpha_ne_of_atom_zero hone
  obtain ⟨K, hK⟩ := exists_nat_gt |t|
  let alphaN : ℕ → Fin A.N → Param :=
    fun n ell ↦ perturbZero (n + K) (A.alpha ell)
  let tauN : ℕ → ProbabilityMeasure Param :=
    fun n ↦ perturbZeroProb tau (n + K)
  let S : ℝ := ∑ ell, A.w ell * singularWeight (A.alpha ell)
  let Sn : ℕ → ℝ := fun n ↦
    ∑ ell, A.w ell * singularWeight (alphaN n ell)
  let D : ℕ → ℝ := fun n ↦ Sn n - S
  let tN : ℕ → ℝ := fun n ↦ t / (1 + t * D n)
  have hmomentEq : MReal (probMeasure tau) = S := by
    rw [A.MReal_eq]
    dsimp only [S]
    apply Finset.sum_congr rfl
    intro ell _
    rw [signedOmega_eq_singularWeight_of_closed_or_upper hastar (hclass ell)]
  have hSle : S ≤ 1 / t := by rwa [← hmomentEq]
  have hbase : 1 ≤ t * S := by
    calc
      1 = t * (1 / t) := by
        rw [mul_one_div]
        exact (div_self (ne_of_lt ht)).symm
      _ ≤ t * S := mul_le_mul_of_nonpos_left hSle ht.le
  have hDformula : ∀ n, D n = ∑ ell, A.w ell *
      (singularWeight (alphaN n ell) - singularWeight (A.alpha ell)) := by
    intro n
    dsimp only [D, Sn, S]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ell _
    ring
  have hdiffNonneg : ∀ n ell,
      0 ≤ singularWeight (alphaN n ell) - singularWeight (A.alpha ell) := by
    intro n ell
    dsimp only [alphaN]
    by_cases hzero : A.alpha ell = 0
    · rw [hzero]
      simp only [perturbZero, if_pos, singularWeight_zero, sub_zero]
      exact (singularWeight_pos_of_Ioo
        ⟨zeroApprox_pos (n + K), zeroApprox_lt_one (n + K)⟩).le
    · rw [perturbZero, if_neg hzero, sub_self]
  have hDnonneg : ∀ n, 0 ≤ D n := by
    intro n
    rw [hDformula]
    exact Finset.sum_nonneg fun ell _ ↦
      mul_nonneg (A.w_pos ell).le (hdiffNonneg n ell)
  have hdiffBound : ∀ n ell,
      singularWeight (alphaN n ell) - singularWeight (A.alpha ell) ≤
        1 / ((n + K + 1 : ℕ) : ℝ) := by
    intro n ell
    dsimp only [alphaN]
    by_cases hzero : A.alpha ell = 0
    · rw [hzero]
      simp only [perturbZero, if_pos, singularWeight_zero, sub_zero,
        zeroApprox_singularWeight]
      exact le_rfl
    · rw [perturbZero, if_neg hzero, sub_self]
      positivity
  have hDupper : ∀ n, D n ≤ 1 / ((n + K + 1 : ℕ) : ℝ) := by
    intro n
    rw [hDformula]
    calc
      (∑ ell, A.w ell *
          (singularWeight (alphaN n ell) - singularWeight (A.alpha ell))) ≤
          ∑ ell, A.w ell * (1 / ((n + K + 1 : ℕ) : ℝ)) := by
            apply Finset.sum_le_sum
            intro ell _
            exact mul_le_mul_of_nonneg_left (hdiffBound n ell) (A.w_pos ell).le
      _ = (1 / ((n + K + 1 : ℕ) : ℝ)) * ∑ ell, A.w ell := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ell _
        ring
      _ = 1 / ((n + K + 1 : ℕ) : ℝ) := by rw [A.w_sum, mul_one]
  have hdenPos : ∀ n, 0 < 1 + t * D n := by
    intro n
    have hdenReal : 0 < ((n + K + 1 : ℕ) : ℝ) := by positivity
    have hKle : (K : ℝ) ≤ ((n + K + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show K ≤ n + K + 1 by omega)
    have habslt : |t| < ((n + K + 1 : ℕ) : ℝ) := hK.trans_le hKle
    have hfrac : |t| * (1 / ((n + K + 1 : ℕ) : ℝ)) < 1 := by
      rw [mul_one_div]
      exact (div_lt_one hdenReal).2 habslt
    have habsD : |t| * D n < 1 :=
      (mul_le_mul_of_nonneg_left (hDupper n) (abs_nonneg t)).trans_lt hfrac
    rw [abs_of_neg ht] at habsD
    nlinarith
  have hSn : Tendsto Sn atTop (𝓝 S) := by
    dsimp only [Sn, S, alphaN]
    exact tendsto_finsetSum Finset.univ fun ell _ ↦
      tendsto_const_nhds.mul
        ((tendsto_singularWeight_perturbZero (A.alpha ell)).comp
          (tendsto_add_atTop_nat K))
  have hD : Tendsto D atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ S) atTop (𝓝 S) := tendsto_const_nhds
    simpa only [D, sub_self] using hSn.sub hconst
  have htN : Tendsto tN atTop (𝓝 t) := by
    have hden : Tendsto (fun n ↦ 1 + t * D n) atTop (𝓝 1) := by
      simpa only [mul_zero, add_zero] using
        tendsto_const_nhds.add (tendsto_const_nhds.mul hD)
    have hnum : Tendsto (fun _ : ℕ ↦ t) atTop (𝓝 t) := tendsto_const_nhds
    have hquot := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
    dsimp only [tN]
    rw [div_one] at hquot
    refine hquot.congr' (Filter.Eventually.of_forall fun _ ↦ rfl)
  have htNneg : ∀ n, tN n < 0 := fun n ↦ div_neg_of_neg_of_pos ht (hdenPos n)
  have hstarExists : ∃ ell, A.alpha ell = astar := by
    by_contra hnone
    push Not at hnone
    have hSnonneg : 0 ≤ S := by
      dsimp only [S]
      exact Finset.sum_nonneg fun ell _ ↦ by
        have hlower : A.alpha ell ∈ Icc (0 : Param) 1 := by
          rcases hclass ell with hlower | hstar
          · exact hlower
          · exact False.elim (hnone ell hstar)
        exact mul_nonneg (A.w_pos ell).le (by
          rw [← toReal_omegaLower_of_Icc hlower]
          exact ENNReal.toReal_nonneg)
    have : 1 / t < 0 := one_div_neg.mpr ht
    linarith
  obtain ⟨ellstar, hellstar⟩ := hstarExists
  have hotherClosed : ∀ ell, ell ≠ ellstar →
      A.alpha ell ∈ Icc (0 : Param) 1 := by
    intro ell hell
    rcases hclass ell with hlower | hstar
    · exact hlower
    · exfalso
      apply hell
      apply A.alpha_injective
      exact hstar.trans hellstar.symm
  have hstarZero : astar ≠ 0 := ne_of_gt
    (lt_trans (show (0 : Param) < 1 by simp) hastar)
  have halphaNStar : ∀ n, alphaN n ellstar = astar := by
    intro n
    dsimp only [alphaN]
    rw [hellstar, perturbZero, if_neg hstarZero]
  have hotherInterior : ∀ n ell, ell ≠ ellstar →
      alphaN n ell ∈ Ioo (0 : Param) 1 := by
    intro n ell hell
    exact perturbZero_Ioo (hotherClosed ell hell) (halphaOne ell)
  have hatomic : ∀ n (p : ProbVec I),
      integratedEntropyPos (probMeasure (tauN n)) p =
        ∑ ell, A.w ell * renyi (alphaN n ell) p := by
    intro n p
    exact A.perturbZero_entropy_eq (n + K) p
  have hcurv : ∀ n, ConvexCone (columnPhi (I := I) (tN n) (tauN n)) := by
    intro n
    have hfactor :
        (∑ ell, tN n * singularWeight (alphaN n ell) * A.w ell) =
          tN n * Sn n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell _
      ring
    have hprod : 1 ≤ tN n * Sn n := by
      change 1 ≤ t / (1 + t * D n) * Sn n
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (hdenPos n)).2
      dsimp only [D]
      nlinarith
    let kstar : Fin (A.N + 1) := Fin.succ ellstar
    have hkpos : 0 < atomicBeta (tN n) (alphaN n) A.w kstar := by
      change 0 < tN n * singularWeight (alphaN n ellstar) * A.w ellstar
      rw [halphaNStar]
      exact mul_pos
        (mul_pos_of_neg_of_neg (htNneg n)
          (singularWeight_neg_of_one_lt hastar))
        (A.w_pos ellstar)
    have hknonpos : ∀ j, j ≠ kstar →
        atomicBeta (tN n) (alphaN n) A.w j ≤ 0 := by
      intro j hj
      cases j using Fin.cases with
      | zero =>
          change 1 - ∑ ell,
            tN n * singularWeight (alphaN n ell) * A.w ell ≤ 0
          rw [hfactor]
          exact sub_nonpos.mpr hprod
      | succ ell =>
          have hell : ell ≠ ellstar := by
            intro heq
            subst ell
            apply hj
            simp only [kstar]
          change tN n * singularWeight (alphaN n ell) * A.w ell ≤ 0
          exact (mul_neg_of_neg_of_pos
            (mul_neg_of_neg_of_pos (htNneg n)
              (singularWeight_pos_of_Ioo (hotherInterior n ell hell)))
            (A.w_pos ell)).le
    apply atomicFactorization_convex (tauN n) (tN n) (alphaN n) A.w
      (hatomic n)
      (fun ell ↦ perturbZero_ne_zero (n + K) (A.alpha ell))
      (fun ell ↦ perturbZero_ne_one (n + K) (halphaOne ell))
      kstar hkpos hknonpos
    · change ConvexCone
        (fun x : ConeVec I ↦ parameterPowerMean (alphaN n ellstar) x)
      rw [halphaNStar]
      exact parameterPowerCurvature.2.1 astar hastar.le
    · intro j hj
      cases j using Fin.cases with
      | zero => exact (l1Mass_concave_convex (I := I)).1
      | succ ell =>
          have hell : ell ≠ ellstar := by
            intro heq
            subst ell
            apply hj
            simp only [kstar]
          exact parameterPowerCurvature.1 (alphaN n ell)
            (hotherInterior n ell hell).2
  apply (pointwiseCurvatureLimit
    (fun n ↦ columnPhi (I := I) (tN n) (tauN n))
    (columnPhi (I := I) t tau) ?_).2 hcurv
  apply A.tendsto_columnPhi_atomic tauN tN alphaN hatomic htN
  intro p ell
  exact (tendsto_renyi_perturbZero p (A.alpha ell)).comp
    (tendsto_add_atTop_nat K)

/-- Literal finite-support sufficiency proposition from the blueprint. Endpoint
atoms are removed by the explicit perturbations above, with the adjusted
temperature used in exactly the two moment-constrained branches. -/
theorem finiteSufficiency
    (tau : ProbabilityMeasure Param)
    (hfin : (suppMeasure (probMeasure tau)).Finite)
    (t : ℝ) (astar : Param)
    {I : Type u} [Fintype I] [Nonempty I] :
    (PosAdm t tau → ConcaveCone (columnPhi (I := I) t tau)) ∧
    (NegLowerAdm t tau → ConvexCone (columnPhi (I := I) t tau)) ∧
    (NegExcAdm t tau astar → ConvexCone (columnPhi (I := I) t tau)) := by
  exact ⟨finiteSufficiency_positive tau hfin t,
    finiteSufficiency_negativeLower tau hfin t,
    finiteSufficiency_negativeExceptional tau hfin t astar⟩

end ConditionalEntropy
