import ConditionalEntropy.ConditionalSemiringOrder
import ConditionalEntropy.MainClassification

/-!
# Paper-facing statements for the complete proof of Sections 4 and 5

This module is the one-to-one public interface between the sixteen numbered
main-text environments in `sections-4-5-full-details.tex` and Lean.  Each
declaration below corresponds to exactly one numbered environment.  Its proof
may use several smaller implementation lemmas; those implementation
dependencies are deliberately kept separate from this paper-facing index.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

/-- Lemma 4.1: curvature of the finite power means, including the maximum
endpoint at order `∞`. -/
theorem fullDetailsLemma4_1 {I : Type u} [Fintype I] [Nonempty I] :
    (∀ a : ℝ, 0 < a → a < 1 →
      ConcaveCone (fun x : ConeVec I => lpNorm a x)) ∧
    (∀ a : ℝ, 1 ≤ a →
      ConvexCone (fun x : ConeVec I => lpNorm a x)) ∧
    ConvexCone (fun x : ConeVec I => finMax x.1) :=
  powerCurvature

/-- Lemma 4.2: exact curvature classification of an affine monomial and its
coordinate monotonicity in every nonzero-sign exponent. -/
theorem fullDetailsLemma4_2 {ι : Type u} [Fintype ι]
    (β : ι → ℝ) (hsum : IsAffineFamily β) :
    (ConcaveOn ℝ (positiveOrthant : Set (ι → ℝ)) (affineMonomial β) ↔
      ∀ i, 0 ≤ β i) ∧
    (ConvexOn ℝ (positiveOrthant : Set (ι → ℝ)) (affineMonomial β) ↔
      HasUniquePositive β) ∧
    (∀ j, 0 < β j → ∀ a ∈ (positiveOrthant : Set (ι → ℝ)),
      ∀ b ∈ (positiveOrthant : Set (ι → ℝ)),
        (∀ i, i ≠ j → a i = b i) → a j < b j →
          affineMonomial β a < affineMonomial β b) ∧
    (∀ j, β j < 0 → ∀ a ∈ (positiveOrthant : Set (ι → ℝ)),
      ∀ b ∈ (positiveOrthant : Set (ι → ℝ)),
        (∀ i, i ≠ j → a i = b i) → a j < b j →
          affineMonomial β b < affineMonomial β a) := by
  rcases affineMonomialCurvaturePackage β hsum with
    ⟨hconc, hconv, _hmono, _hanti, hstrictMono, hstrictAnti⟩
  exact ⟨hconc, hconv, hstrictMono, hstrictAnti⟩

/-- Lemma 4.3: all three finite-support sufficient-condition branches.  The
admissibility predicates spell out the support, endpoint, and guarded moment
conditions used in the paper. -/
theorem fullDetailsLemma4_3
    (tau : ProbabilityMeasure Param)
    (hfin : (suppMeasure (probMeasure tau)).Finite)
    (t : ℝ) (_ht : t ≠ 0)
    {I : Type u} [Fintype I] [Nonempty I] :
    (PosAdm t tau → ConcaveCone (columnPhi (I := I) t tau)) ∧
    (NegLowerAdm t tau → ConvexCone (columnPhi (I := I) t tau)) ∧
    ((∃ astar : Param, NegExcAdm t tau astar) →
      ConvexCone (columnPhi (I := I) t tau)) := by
  refine ⟨(finiteSufficiency tau hfin t (0 : Param)).1,
    (finiteSufficiency tau hfin t (0 : Param)).2.1, ?_⟩
  rintro ⟨astar, hastar⟩
  exact (finiteSufficiency tau hfin t astar).2.2 hastar

/-- Proposition 4.4: arbitrary-measure temperate sufficiency in all three
parameter branches. -/
theorem fullDetailsProposition4_4
    (tau : ProbabilityMeasure Param) (t : ℝ) (_ht : t ≠ 0)
    {I : Type u} [Fintype I] [Nonempty I] :
    (PosAdm t tau → ConcaveCone (columnPhi (I := I) t tau)) ∧
    (NegLowerAdm t tau → ConvexCone (columnPhi (I := I) t tau)) ∧
    ((∃ astar : Param, NegExcAdm t tau astar) →
      ConvexCone (columnPhi (I := I) t tau)) := by
  refine ⟨(generalSufficiency tau t (0 : Param)).1,
    (generalSufficiency tau t (0 : Param)).2.1, ?_⟩
  rintro ⟨astar, hastar⟩
  exact (generalSufficiency tau t astar).2.2 hastar

/-- Proposition 4.5: negative-tropical sufficiency. -/
theorem fullDetailsProposition4_5 (tau : ProbabilityMeasure Param) :
    DMinus tau → CMMonotone (HMinus tau : PolyJointFunctional.{u}) :=
  negativeTropicalSufficiency tau

/-- Proposition 4.6: the positive-tropical candidate is the maximum of the
order-zero conditional entropies and is monotone. -/
theorem fullDetailsProposition4_6 :
    (∀ {X Y : Type u} [Fintype X] [Nonempty X]
      [Fintype Y] [Nonempty Y] (P : JointProb X Y),
        HPlus (diracProb 0) P =
          (letI := activeNonempty P
           finMax (fun y : Active P => renyi 0 (conditional P y)))) ∧
    CMMonotone (HPlus (diracProb 0) : PolyJointFunctional.{u}) := by
  exact ⟨fun P => positiveTropicalComponent P, positiveTropicalSufficiency⟩

/-- Proposition 4.7: every finite positive mixture supported on `[0,1]`
defines a monotone derivation candidate; the Dirac measures give the stated
extremal family as an explicit corollary. -/
theorem fullDetailsProposition4_7
    (sigma : FiniteMeasure Param)
    (hsupp : suppMeasure (finiteMeasure sigma) ⊆ Icc (0 : Param) 1) :
    CMMonotone (HZero sigma : PolyJointFunctional.{u}) ∧
      (∀ alpha : Param, alpha ≤ 1 →
        CMMonotone
            (HZero (diracProb alpha).toFiniteMeasure :
              PolyJointFunctional.{u}) ∧
          ∀ {X Y : Type u} [Fintype X] [Nonempty X]
            [Fintype Y] [Nonempty Y] (P : JointProb X Y),
            HZero (diracProb alpha).toFiniteMeasure P =
              ∑ y : Active P,
                colMass P y.1 * renyi alpha (conditional P y)) := by
  have hgeneral : ∀ (rho : FiniteMeasure Param),
      suppMeasure (finiteMeasure rho) ⊆ Icc (0 : Param) 1 →
        CMMonotone (HZero rho : PolyJointFunctional.{u}) := by
    intro rho hrho
    have h :
        CMMonotone (derivationFamily rho : PolyJointFunctional.{u}) ∧
          (derivationFamily rho : PolyJointFunctional.{u}) =
            (HZero rho : PolyJointFunctional.{u}) :=
      derivationSufficiency rho hrho
    intro X Y Y' _ _ _ _ _ _ P Q hPQ
    have hmono := h.1 P Q hPQ
    rw [h.2] at hmono
    exact hmono
  refine ⟨hgeneral sigma hsupp, ?_⟩
  intro alpha halpha
  have halphaSupp : suppMeasure
      (finiteMeasure (diracProb alpha).toFiniteMeasure) ⊆
        Icc (0 : Param) 1 := by
    change suppMeasure (diracRaw alpha) ⊆ Icc (0 : Param) 1
    rw [suppMeasure, support_diracRaw]
    simpa only [singleton_subset_iff, mem_Icc] using
      (show (0 : Param) ≤ alpha ∧ alpha ≤ 1 from ⟨bot_le, halpha⟩)
  refine ⟨hgeneral _ halphaSupp, ?_⟩
  intro X Y _ _ _ _ P
  unfold HZero
  change (∑ y : Active P, colMass P y.1 *
      integratedEntropyPos (diracRaw alpha) (conditional P y)) = _
  simp only [integratedEntropyPos_dirac]

/-- Proposition 5.1: positive curvature forces the lower support, vanishing
Shannon atom, and sharp lower-moment bound. -/
theorem fullDetailsProposition5_1
    (nu : FiniteMeasure Param) (hconc : PosPhiConcave.{u} nu) :
    suppMeasure (finiteMeasure nu) ⊆ Icc 0 1 ∧
      finiteMeasure nu ({1} : Set Param) = 0 ∧
      MLower (finiteMeasure nu) ≤ ENNReal.ofReal 1 :=
  positiveNecessity nu hconc

/-- Proposition 5.2: a nonzero Shannon atom in a negative witness excludes
all support strictly above order one. -/
theorem fullDetailsProposition5_2
    (nu : FiniteMeasure Param)
    (hatom : finiteMeasure nu ({1} : Set Param) ≠ 0)
    (hconv : NegPhiConvex.{u} nu) :
    suppMeasure (finiteMeasure nu) ⊆ Icc (0 : Param) 1 :=
  negativeShannonObstruction nu hatom hconv

/-- Proposition 5.3: the local truncated-moment inequality, together with its
stated global corollary.  Here `nu` is the positive magnitude of the paper's
negative measure, so the paper's signed moment is `-MReal (finiteMeasure nu)`.
-/
theorem fullDetailsProposition5_3
    (nu : FiniteMeasure Param)
    (hatom : finiteMeasure nu ({1} : Set Param) = 0)
    (hconv : NegPhiConvex.{u} nu) :
    (∀ {a b : ℝ}, 0 < a → a < 1 → 1 < b →
      finiteMeasure nu ({finiteParam a} : Set Param) = 0 →
      finiteMeasure nu ({finiteParam b} : Set Param) = 0 →
      0 < finiteMeasure nu (Ioi (finiteParam b)) →
      1 ≤ upperTrunc nu b - lowerTrunc nu a) ∧
    (MomFin (finiteMeasure nu) →
      -MReal (finiteMeasure nu) < 1 →
      suppMeasure (finiteMeasure nu) ⊆ Icc (0 : Param) 1) := by
  constructor
  · intro a b ha ha1 hb1 hnullA hnullB htail
    exact (truncatedMoment nu hatom hconv ha ha1 hb1 hnullA hnullB htail).1
  · intro _hMom hstrict
    rcases negativeTemperateNecessity_of_atom_zero nu hconv hatom with
      hlower | ⟨_astar, _hastar, _hsupp, _hatom, _hLower, _hMom', hmoment⟩
    · exact hlower
    · exfalso
      linarith

/-- Remark 5.4: the formal content used to justify unnormalised one-column
witnesses—degree-one homogeneity, the quotient channel comparison, and the
embedding lift. -/
theorem fullDetailsRemark5_4 :
    (∀ {I : Type u} [Fintype I] [Nonempty I]
      (t : ℝ) (tau : ProbabilityMeasure Param),
        PosHomOne (columnPhi t tau : ConeVec I → ℝ)) ∧
    (∀ {I : Type u} [Fintype I] [Nonempty I]
      (sigma : FiniteMeasure Param),
        PosHomOne (columnDeriv sigma : ConeVec I → ℝ)) ∧
    (∀ {X Y Y' : Type u} [Fintype X] [Fintype Y] [Fintype Y']
      {P : JointProb X Y} {Q : JointProb X Y'},
        CMRel P Q →
          conditionalSemiringOfJointProb P ≤ conditionalSemiringOfJointProb Q) ∧
    (∀ F : PolyJointFunctional.{u},
      JointEmbeddingInvariant F → CMMonotone F → CEmbedsMonotone F) := by
  exact ⟨fun t tau => columnPhi_posHomOne t tau,
    fun sigma => columnDeriv_posHomOne sigma,
    fun h => conditionalSemiringOfJointProb_le h,
    fun F => embeddingLift F⟩

/-! ## The compensated fixed-mass construction of Remark 5.5 -/

/-- The paper's first affine column `x + lambda v`, bundled with the supplied
proof that it remains nonnegative. -/
def affinePerturbedColumn {I : Type u}
    (x : ConeVec I) (v : I → ℝ) (lambda : ℝ)
    (hnonneg : Nonneg (fun i => x.1 i + lambda * v i)) : ConeVec I :=
  ⟨fun i => x.1 i + lambda * v i, hnonneg⟩

/-- The paper's compensated second column
`x' - lambda * normalize(x') * sum_i v_i`, written as a nonnegative scaling
of `x'`. -/
def compensatedSecondColumn {I : Type u} [Fintype I]
    (x' : ConeVec I) (v : I → ℝ) (lambda : ℝ)
    (_hmass : 0 < l1Mass x'.1)
    (hscale : 0 ≤ 1 - lambda * (∑ i, v i) / l1Mass x'.1) : ConeVec I :=
  coneScale (1 - lambda * (∑ i, v i) / l1Mass x'.1) hscale x'

theorem l1Mass_affinePerturbedColumn {I : Type u} [Fintype I]
    (x : ConeVec I) (v : I → ℝ) (lambda : ℝ)
    (hnonneg : Nonneg (fun i => x.1 i + lambda * v i)) :
    l1Mass (affinePerturbedColumn x v lambda hnonneg).1 =
      l1Mass x.1 + lambda * ∑ i, v i := by
  simp [affinePerturbedColumn, l1Mass, Finset.sum_add_distrib,
    ← Finset.mul_sum]

theorem l1Mass_compensatedSecondColumn {I : Type u} [Fintype I]
    (x' : ConeVec I) (v : I → ℝ) (lambda : ℝ)
    (hmass : 0 < l1Mass x'.1)
    (hscale : 0 ≤ 1 - lambda * (∑ i, v i) / l1Mass x'.1) :
    l1Mass (compensatedSecondColumn x' v lambda hmass hscale).1 =
      l1Mass x'.1 - lambda * ∑ i, v i := by
  rw [compensatedSecondColumn, l1Mass_coneScale]
  field_simp [hmass.ne']

theorem compensatedSecondColumn_apply {I : Type u} [Fintype I]
    (x' : ConeVec I) (v : I → ℝ) (lambda : ℝ)
    (hmass : 0 < l1Mass x'.1)
    (hscale : 0 ≤ 1 - lambda * (∑ i, v i) / l1Mass x'.1)
    (i : I) :
    (compensatedSecondColumn x' v lambda hmass hscale).1 i =
      x'.1 i - lambda * (x'.1 i / l1Mass x'.1) * ∑ j, v j := by
  change (1 - lambda * (∑ j, v j) / l1Mass x'.1) * x'.1 i = _
  field_simp [hmass.ne']

theorem posHomOne_compensatedSecondColumn {I : Type u} [Fintype I]
    (F : ConeVec I → ℝ) (hF : PosHomOne F)
    (x' : ConeVec I) (v : I → ℝ) (lambda : ℝ)
    (hmass : 0 < l1Mass x'.1)
    (hscale : 0 ≤ 1 - lambda * (∑ i, v i) / l1Mass x'.1) :
    F (compensatedSecondColumn x' v lambda hmass hscale) =
      (1 - lambda * (∑ i, v i) / l1Mass x'.1) * F x' :=
  hF x' _ hscale

/-- Adding an affine correction does not change a scalar curve's second
derivative.  This is the calculus step used by the fixed-mass construction. -/
private theorem secondDeriv_add_affine
    (g : ℝ → ℝ) (A B lambda : ℝ)
    (hg : ∀ s, DifferentiableAt ℝ g s)
    (hg' : DifferentiableAt ℝ (deriv g) lambda) :
    secondDeriv (fun s => g s + (A + B * s)) lambda =
      secondDeriv g lambda := by
  have haffine : ∀ s : ℝ,
      HasDerivAt (fun r : ℝ => A + B * r) B s := by
    intro s
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id s).const_mul B).const_add A
  have hderiv :
      deriv (fun s => g s + (A + B * s)) =
        fun s => deriv g s + B := by
    funext s
    exact ((hg s).hasDerivAt.add (haffine s)).deriv
  unfold secondDeriv
  rw [hderiv]
  exact (hg'.hasDerivAt.add_const B).deriv

/-- Remark 5.5: the compensated column is exactly the displayed paper
formula, the two-column mass is constant, and every degree-one homogeneous
functional contributes only the displayed affine correction on the second
column.  The additive two-column value is written explicitly, and the final
clause verifies that this affine correction leaves the second derivative of
the first-column contribution unchanged. -/
theorem fullDetailsRemark5_5 {I : Type u} [Fintype I]
    (F : ConeVec I → ℝ) (hF : PosHomOne F)
    (x x' : ConeVec I) (v : I → ℝ) (lambda : ℝ)
    (hmass : 0 < l1Mass x'.1)
    (hfirst : Nonneg (fun i => x.1 i + lambda * v i))
    (hscale : 0 ≤ 1 - lambda * (∑ i, v i) / l1Mass x'.1) :
    (∀ i,
      (compensatedSecondColumn x' v lambda hmass hscale).1 i =
        x'.1 i - lambda * (x'.1 i / l1Mass x'.1) * ∑ j, v j) ∧
    (l1Mass (affinePerturbedColumn x v lambda hfirst).1 +
        l1Mass (compensatedSecondColumn x' v lambda hmass hscale).1 =
      l1Mass x.1 + l1Mass x'.1) ∧
    (F (compensatedSecondColumn x' v lambda hmass hscale) =
      (1 - lambda * (∑ i, v i) / l1Mass x'.1) * F x') ∧
    (F (affinePerturbedColumn x v lambda hfirst) +
        F (compensatedSecondColumn x' v lambda hmass hscale) =
      F (affinePerturbedColumn x v lambda hfirst) + F x' -
        lambda * ((∑ i, v i) / l1Mass x'.1) * F x') ∧
    (∀ (g : ℝ → ℝ), (∀ s, DifferentiableAt ℝ g s) →
      DifferentiableAt ℝ (deriv g) lambda →
      secondDeriv
          (fun s => g s +
            (1 - s * ((∑ i, v i) / l1Mass x'.1)) * F x') lambda =
        secondDeriv g lambda) := by
  have hcorrection :=
    posHomOne_compensatedSecondColumn F hF x' v lambda hmass hscale
  refine ⟨fun i => compensatedSecondColumn_apply x' v lambda hmass hscale i,
    ?_, hcorrection, ?_, ?_⟩
  · rw [l1Mass_affinePerturbedColumn,
      l1Mass_compensatedSecondColumn]
    ring
  · rw [hcorrection]
    ring
  · intro g hg hg'
    let c : ℝ := (∑ i, v i) / l1Mass x'.1
    have hfun :
        (fun s => g s + (1 - s * c) * F x') =
          fun s => g s + (F x' + (-c * F x') * s) := by
      funext s
      ring
    rw [show (∑ i, v i) / l1Mass x'.1 = c from rfl, hfun]
    exact secondDeriv_add_affine g (F x') (-c * F x') lambda hg hg'

/-- Proposition 5.6: complete exceptional negative-temperate necessity after
the Shannon atom has vanished. -/
theorem fullDetailsProposition5_6
    (nu : FiniteMeasure Param) (hconv : NegPhiConvex.{u} nu)
    (hatom : finiteMeasure nu ({1} : Set Param) = 0) :
    suppMeasure (finiteMeasure nu) ⊆ Icc (0 : Param) 1 ∨
      ∃ astar : Param, (1 : Param) < astar ∧
        suppMeasure (finiteMeasure nu) ⊆
          Icc (0 : Param) 1 ∪ {astar} ∧
        finiteMeasure nu ({1} : Set Param) = 0 ∧
        MLower (finiteMeasure nu) < ⊤ ∧
        MomFin (finiteMeasure nu) ∧
        MReal (finiteMeasure nu) ≤ -1 :=
  negativeTemperateNecessity_of_atom_zero nu hconv hatom

/-- Proposition 5.7: negative-tropical necessity. -/
theorem fullDetailsProposition5_7 (tau : ProbabilityMeasure Param) :
    CMMonotone (HMinus tau : PolyJointFunctional.{u}) → DMinus tau :=
  negativeTropicalNecessity tau

/-- Proposition 5.8: positive-tropical necessity. -/
theorem fullDetailsProposition5_8 (tau : ProbabilityMeasure Param) :
    CMMonotone (HPlus tau : PolyJointFunctional.{u}) → tau = diracProb 0 :=
  positiveTropicalNecessity tau

/-- Proposition 5.9: concavity of the represented derivation column excludes
all parameter support above order one, together with the paper's explicit
Dirac/extremal specialization. -/
theorem fullDetailsProposition5_9
    (nu : FiniteMeasure Param)
    (hconcave : ∀ {I : Type u} [Fintype I] [Nonempty I],
      ConcaveCone (derivationColumn nu : ConeVec I → ℝ)) :
    suppMeasure (finiteMeasure nu) ⊆ Icc 0 1 ∧
      (∀ alpha : Param,
        (∀ {I : Type u} [Fintype I] [Nonempty I],
          ConcaveCone
            (derivationColumn (diracProb alpha).toFiniteMeasure :
              ConeVec I → ℝ)) →
        alpha ≤ 1) ∧
      (∀ (alpha : Param) {I : Type u} [Fintype I] [Nonempty I]
        (x : ConeVec I),
        derivationColumn (diracProb alpha).toFiniteMeasure x =
          perspective (renyi alpha : ProbVec I → ℝ) x) := by
  refine ⟨derivationNecessity nu hconcave, ?_, ?_⟩
  · intro alpha halphaConcave
    have hsupp :=
      derivationNecessity (diracProb alpha).toFiniteMeasure halphaConcave
    have halphaSupport : alpha ∈
        suppMeasure
          (finiteMeasure (diracProb alpha).toFiniteMeasure) := by
      change alpha ∈ suppMeasure (diracRaw alpha)
      rw [suppMeasure, support_diracRaw]
      exact mem_singleton alpha
    exact (hsupp halphaSupport).2
  · intro alpha I _ _ x
    change columnDeriv (diracProb alpha).toFiniteMeasure x =
      perspective (renyi alpha : ProbVec I → ℝ) x
    by_cases hx : x = 0
    · subst x
      rw [columnDeriv_zero]
      exact (perspective_zero (renyi alpha : ProbVec I → ℝ)).symm
    · rw [columnDeriv_of_ne _ x hx,
        perspective_of_ne (renyi alpha : ProbVec I → ℝ) x hx]
      change l1Mass x.1 * integratedEntropyPos (diracRaw alpha)
          (normalize (toPosCone x hx)) =
        l1Mass x.1 * renyi alpha (normalize (toPosCone x hx))
      rw [integratedEntropyPos_dirac]

end ConditionalEntropy
