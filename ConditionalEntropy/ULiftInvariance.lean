import ConditionalEntropy.FiniteSemiring
import ConditionalEntropy.IntegratedEntropyAlgebra
import ConditionalEntropy.SignedWitnesses

/-!
# Universe-lift invariance of finite cone functionals

The canonical equivalence with `ULift` reindexes finite cone vectors without
changing their mass or normalized entropy.  The resulting transport lemmas let
global shape hypotheses at one universe level be applied to finite carriers
living at a lower universe level.
-/

noncomputable section

open MeasureTheory Set

namespace ConditionalEntropy

universe u v

/-- Reindex a cone vector along the canonical equivalence with `ULift`. -/
def uliftCone {I : Type v} [Fintype I]
    (x : ConeVec I) : ConeVec (ULift.{u, v} I) :=
  zeroExtendCone Equiv.ulift.symm.toEmbedding x

@[simp] theorem uliftCone_apply {I : Type v} [Fintype I]
    (x : ConeVec I) (i : I) :
    (uliftCone x).1 (ULift.up i) = x.1 i := by
  exact zeroExtendRaw_apply Equiv.ulift.symm.toEmbedding x.1 i

@[simp] theorem uliftCone_zero {I : Type v} [Fintype I] :
    uliftCone (0 : ConeVec I) = 0 := by
  apply Subtype.ext
  funext j
  rcases j with ⟨i⟩
  simp

theorem uliftCone_injective {I : Type v} [Fintype I] :
    Function.Injective (uliftCone :
      ConeVec I → ConeVec (ULift.{u, v} I)) := by
  intro x y hxy
  apply Subtype.ext
  funext i
  have h := congrFun (congrArg Subtype.val hxy) (ULift.up i)
  simpa using h

@[simp] theorem uliftCone_eq_zero_iff {I : Type v} [Fintype I]
    (x : ConeVec I) : uliftCone x = 0 ↔ x = 0 := by
  constructor
  · intro h
    exact uliftCone_injective (h.trans uliftCone_zero.symm)
  · rintro rfl
    exact uliftCone_zero

@[simp] theorem l1Mass_uliftCone {I : Type v} [Fintype I]
    (x : ConeVec I) :
    l1Mass (uliftCone x).1 = l1Mass x.1 := by
  exact sum_zeroExtendRaw Equiv.ulift.symm.toEmbedding x.1

/-- Reindex a punctured-cone vector along the canonical `ULift` equivalence. -/
def uliftPosCone {I : Type v} [Fintype I]
    (x : PosConeVec I) : PosConeVec (ULift.{u, v} I) :=
  ⟨uliftCone x.1, by
    intro hzero
    apply x.2
    funext i
    have hi := congrFun hzero (ULift.up i)
    simpa using hi⟩

@[simp] theorem uliftPosCone_apply {I : Type v} [Fintype I]
    (x : PosConeVec I) (i : I) :
    (uliftPosCone x).1.1 (ULift.up i) = x.1.1 i := by
  simp [uliftPosCone]

/-- Normalization commutes with the canonical universe lift. -/
theorem normalize_uliftPosCone {I : Type v} [Fintype I] [Nonempty I]
    (x : PosConeVec I) :
    normalize (uliftPosCone x) =
      zeroExtendProb Equiv.ulift.symm.toEmbedding (normalize x) := by
  apply Subtype.ext
  funext j
  rcases j with ⟨i⟩
  change (uliftCone x.1).1 (ULift.up i) / l1Mass (uliftCone x.1).1 =
    zeroExtendRaw Equiv.ulift.symm.toEmbedding (normalize x).1 (ULift.up i)
  rw [uliftCone_apply, l1Mass_uliftCone]
  change (normalize x).1 i =
    zeroExtendRaw Equiv.ulift.symm.toEmbedding (normalize x).1 (ULift.up i)
  exact (zeroExtendRaw_apply Equiv.ulift.symm.toEmbedding (normalize x).1 i).symm

/-- `toPosCone` commutes with the canonical universe lift. -/
theorem toPosCone_uliftCone {I : Type v} [Fintype I]
    (x : ConeVec I) (hx : x ≠ 0) :
    toPosCone (uliftCone x)
        ((uliftCone_eq_zero_iff x).not.mpr hx) =
      uliftPosCone (toPosCone x hx) := by
  apply Subtype.ext
  rfl

/-- Universe lifting commutes with convex mixing in the cone. -/
theorem uliftCone_coneMix {I : Type v} [Fintype I]
    (lambda : ℝ) (hlambda : lambda ∈ Icc (0 : ℝ) 1)
    (x z : ConeVec I) :
    uliftCone (coneMix lambda hlambda x z) =
      coneMix lambda hlambda (uliftCone x)
        (uliftCone z) := by
  apply Subtype.ext
  funext j
  rcases j with ⟨i⟩
  simp [coneMix]

/-- Universe lifting commutes with strict mixing in the punctured cone. -/
theorem uliftPosCone_posMix {I : Type v} [Fintype I]
    (lambda : ℝ) (hlambda : 0 < lambda ∧ lambda < 1)
    (x z : PosConeVec I) :
    uliftPosCone (posMix lambda hlambda x z) =
      posMix lambda hlambda (uliftPosCone x)
        (uliftPosCone z) := by
  apply Subtype.ext
  apply Subtype.ext
  funext j
  rcases j with ⟨i⟩
  simp [posMix, coneMix]

/-- A cone concavity inequality on the lifted carrier descends to the original
carrier whenever the two functions agree under the canonical lift. -/
theorem concaveCone_of_ulift {I : Type v} [Fintype I]
    (F : ConeVec I → ℝ)
    (Fup : ConeVec (ULift.{u, v} I) → ℝ)
    (hinv : ∀ x, Fup (uliftCone x) = F x)
    (hconc : ConcaveCone Fup) : ConcaveCone F := by
  intro x z lambda hlambda
  rw [← hinv x, ← hinv z, ← hinv (coneMix lambda hlambda x z),
    uliftCone_coneMix]
  exact hconc _ _ lambda hlambda

/-- A cone convexity inequality on the lifted carrier descends to the original
carrier whenever the two functions agree under the canonical lift. -/
theorem convexCone_of_ulift {I : Type v} [Fintype I]
    (F : ConeVec I → ℝ)
    (Fup : ConeVec (ULift.{u, v} I) → ℝ)
    (hinv : ∀ x, Fup (uliftCone x) = F x)
    (hconv : ConvexCone Fup) : ConvexCone F := by
  intro x z lambda hlambda
  rw [← hinv x, ← hinv z, ← hinv (coneMix lambda hlambda x z),
    uliftCone_coneMix]
  exact hconv _ _ lambda hlambda

/-- Quasi-convexity on the lifted punctured cone descends along `ULift`. -/
theorem qCvx_of_ulift {I : Type v} [Fintype I]
    (g : PosConeVec I → ℝ)
    (gup : PosConeVec (ULift.{u, v} I) → ℝ)
    (hinv : ∀ x, gup (uliftPosCone x) = g x)
    (hqcvx : QCvx gup) : QCvx g := by
  intro x z lambda hlambda
  rw [← hinv x, ← hinv z, ← hinv (posMix lambda hlambda x z),
    uliftPosCone_posMix]
  exact hqcvx _ _ lambda hlambda

/-- The linear entropy perspective is invariant under universe lifting. -/
theorem derivationColumn_ulift {I : Type v} [Fintype I] [Nonempty I]
    (nu : FiniteMeasure Param) (x : ConeVec I) :
    columnDeriv nu (uliftCone x) = columnDeriv nu x := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  by_cases hx : x = 0
  · subst x
    simp
  · have hxup : uliftCone x ≠ 0 :=
      (uliftCone_eq_zero_iff x).not.mpr hx
    rw [columnDeriv_of_ne nu _ hxup, columnDeriv_of_ne nu x hx,
      l1Mass_uliftCone, toPosCone_uliftCone,
      normalize_uliftPosCone, integratedEntropyPos_zeroExtend]

/-- The exponential signed perspective is invariant under universe lifting. -/
theorem PhiSigned_ulift {I : Type v} [Fintype I] [Nonempty I]
    (mu : SignedMeasure Param) (x : ConeVec I) :
    PhiSigned mu (uliftCone x) = PhiSigned mu x := by
  by_cases hx : x = 0
  · subst x
    simp
  · have hxup : uliftCone x ≠ 0 :=
      (uliftCone_eq_zero_iff x).not.mpr hx
    rw [PhiSigned_of_ne mu _ hxup, PhiSigned_of_ne mu x hx,
      l1Mass_uliftCone, toPosCone_uliftCone,
      normalize_uliftPosCone, integratedEntropySigned_zeroExtend]

/-- The normalized signed entropy is invariant under universe lifting. -/
theorem GSigned_ulift {I : Type v} [Fintype I] [Nonempty I]
    (mu : SignedMeasure Param) (x : PosConeVec I) :
    GSigned mu (uliftPosCone x) = GSigned mu x := by
  unfold GSigned
  rw [normalize_uliftPosCone, integratedEntropySigned_zeroExtend]

/-- Specialized descent of concavity for the linear entropy perspective. -/
theorem concaveCone_derivationColumn_of_ulift
    {I : Type v} [Fintype I] [Nonempty I]
    (nu : FiniteMeasure Param)
    (hconc : ConcaveCone
      (columnDeriv nu : ConeVec (ULift.{u, v} I) → ℝ)) :
    ConcaveCone (columnDeriv nu : ConeVec I → ℝ) :=
  concaveCone_of_ulift _ _ (derivationColumn_ulift nu) hconc

/-- Specialized descent of concavity for the signed exponential perspective. -/
theorem concaveCone_PhiSigned_of_ulift
    {I : Type v} [Fintype I] [Nonempty I]
    (mu : SignedMeasure Param)
    (hconc : ConcaveCone
      (PhiSigned mu : ConeVec (ULift.{u, v} I) → ℝ)) :
    ConcaveCone (PhiSigned mu : ConeVec I → ℝ) :=
  concaveCone_of_ulift _ _ (PhiSigned_ulift mu) hconc

/-- Specialized descent of convexity for the signed exponential perspective. -/
theorem convexCone_PhiSigned_of_ulift
    {I : Type v} [Fintype I] [Nonempty I]
    (mu : SignedMeasure Param)
    (hconv : ConvexCone
      (PhiSigned mu : ConeVec (ULift.{u, v} I) → ℝ)) :
    ConvexCone (PhiSigned mu : ConeVec I → ℝ) :=
  convexCone_of_ulift _ _ (PhiSigned_ulift mu) hconv

/-- Specialized descent of quasi-convexity for normalized signed entropy. -/
theorem qCvx_GSigned_of_ulift
    {I : Type v} [Fintype I] [Nonempty I]
    (mu : SignedMeasure Param)
    (hqcvx : QCvx
      (GSigned mu : PosConeVec (ULift.{u, v} I) → ℝ)) :
    QCvx (GSigned mu : PosConeVec I → ℝ) :=
  qCvx_of_ulift _ _ (GSigned_ulift mu) hqcvx

end ConditionalEntropy
