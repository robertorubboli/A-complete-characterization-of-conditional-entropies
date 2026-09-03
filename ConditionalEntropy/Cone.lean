import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-!
# The nonnegative cone and elementary curvature rules

This module implements the proof-carrying cone interface and elementary
curvature rules used in Sections 4 and 5 of the manuscript.  Only ordinary
Mathlib structures are used: in particular, the cone is an additive submonoid
and is deliberately not given an additive-group or module structure.
-/

open Set

namespace ConditionalEntropy

universe u v

/-- Coordinatewise nonnegativity of a real-valued vector. -/
def Nonneg {I : Type u} (x : I → ℝ) : Prop :=
  ∀ i, 0 ≤ x i

/-- The additive submonoid of coordinatewise nonnegative vectors. -/
def NonnegAddSubmonoid (I : Type u) : AddSubmonoid (I → ℝ) where
  carrier := {x | Nonneg x}
  zero_mem' := by
    intro i
    exact le_rfl
  add_mem' := by
    intro x z hx hz i
    exact add_nonneg (hx i) (hz i)

/-- A proof-carrying vector in the closed nonnegative cone. -/
abbrev ConeVec (I : Type u) := NonnegAddSubmonoid I

/-- A proof-carrying nonnegative vector whose underlying function is nonzero. -/
def PosConeVec (I : Type u) :=
  {x : ConeVec I // x.1 ≠ (0 : I → ℝ)}

/-- Nonnegative scalar multiplication, bundled back into the cone. -/
def coneScale {I : Type u} (c : ℝ) (hc : 0 ≤ c) (x : ConeVec I) : ConeVec I :=
  ⟨fun i => c * x.1 i, fun i => mul_nonneg hc (x.2 i)⟩

/-- A convex combination, bundled back into the cone. -/
def coneMix {I : Type u} (lambda : ℝ) (hlambda : lambda ∈ Icc (0 : ℝ) 1)
    (x z : ConeVec I) : ConeVec I :=
  ⟨fun i => lambda * x.1 i + (1 - lambda) * z.1 i, fun i =>
    add_nonneg (mul_nonneg hlambda.1 (x.2 i))
      (mul_nonneg (sub_nonneg.mpr hlambda.2) (z.2 i))⟩

/-- Positive scalar multiplication preserves the punctured cone. -/
def posScale {I : Type u} (c : ℝ) (hc : 0 < c) (x : PosConeVec I) : PosConeVec I :=
  ⟨coneScale c hc.le x.1, by
    intro hs
    apply x.2
    funext i
    have hi : c * x.1.1 i = 0 := by
      simpa [coneScale] using congrFun hs i
    exact (mul_eq_zero.mp hi).resolve_left hc.ne'⟩

/-- A strict convex combination of punctured-cone vectors remains nonzero. -/
def posMix {I : Type u} (lambda : ℝ) (hlambda : 0 < lambda ∧ lambda < 1)
    (x z : PosConeVec I) : PosConeVec I :=
  ⟨coneMix lambda ⟨hlambda.1.le, hlambda.2.le⟩ x.1 z.1, by
    intro hs
    apply x.2
    funext i
    have hi : lambda * x.1.1 i + (1 - lambda) * z.1.1 i = 0 := by
      simpa [coneMix] using congrFun hs i
    have hz : 0 ≤ (1 - lambda) * z.1.1 i :=
      mul_nonneg (sub_nonneg.mpr hlambda.2.le) (z.1.2 i)
    have hxle : lambda * x.1.1 i ≤ 0 := by
      calc
        lambda * x.1.1 i ≤ lambda * x.1.1 i + (1 - lambda) * z.1.1 i :=
          le_add_of_nonneg_right hz
        _ = 0 := hi
    have hxzero : lambda * x.1.1 i = 0 :=
      le_antisymm hxle (mul_nonneg hlambda.1.le (x.1.2 i))
    exact (mul_eq_zero.mp hxzero).resolve_left hlambda.1.ne'⟩

/-- Convert subtype nonzeroness into the underlying-function proof carried by
`PosConeVec`. -/
def toPosCone {I : Type u} (x : ConeVec I) (hx : x ≠ 0) : PosConeVec I :=
  ⟨x, by
    intro hzero
    apply hx
    apply Subtype.ext
    exact hzero⟩

/-- Positive homogeneity of degree one on the proof-carrying cone. -/
def PosHomOne {I : Type u} (F : ConeVec I → ℝ) : Prop :=
  ∀ x : ConeVec I, ∀ c : ℝ, ∀ hc : 0 ≤ c,
    F (coneScale c hc x) = c * F x

/-- Concavity expressed using the cone's proof-carrying convex combination. -/
def ConcaveCone {I : Type u} (F : ConeVec I → ℝ) : Prop :=
  ∀ x z : ConeVec I, ∀ lambda : ℝ, ∀ hlambda : lambda ∈ Icc (0 : ℝ) 1,
    lambda * F x + (1 - lambda) * F z ≤ F (coneMix lambda hlambda x z)

/-- Convexity expressed using the cone's proof-carrying convex combination. -/
def ConvexCone {I : Type u} (F : ConeVec I → ℝ) : Prop :=
  ∀ x z : ConeVec I, ∀ lambda : ℝ, ∀ hlambda : lambda ∈ Icc (0 : ℝ) 1,
    F (coneMix lambda hlambda x z) ≤ lambda * F x + (1 - lambda) * F z

/-- Extension of either curvature inequality from the punctured cone to the
origin, for a degree-one positively homogeneous function vanishing there. -/
theorem originExtension {I : Type u} [Nonempty I]
    (F : ConeVec I → ℝ) (hFzero : F 0 = 0) (hFhom : PosHomOne F) :
    ((∀ x z : ConeVec I, x ≠ 0 → z ≠ 0 →
        ∀ lambda : ℝ, ∀ hlambda : lambda ∈ Icc (0 : ℝ) 1,
          lambda * F x + (1 - lambda) * F z ≤ F (coneMix lambda hlambda x z)) →
      ConcaveCone F) ∧
    ((∀ x z : ConeVec I, x ≠ 0 → z ≠ 0 →
        ∀ lambda : ℝ, ∀ hlambda : lambda ∈ Icc (0 : ℝ) 1,
          F (coneMix lambda hlambda x z) ≤ lambda * F x + (1 - lambda) * F z) →
      ConvexCone F) := by
  constructor
  · intro hpunctured x z lambda hlambda
    by_cases hx : x = 0
    · subst x
      have hmix : coneMix lambda hlambda 0 z =
          coneScale (1 - lambda) (sub_nonneg.mpr hlambda.2) z := by
        ext i
        simp [coneMix, coneScale]
      rw [hmix, hFhom z (1 - lambda) (sub_nonneg.mpr hlambda.2), hFzero]
      simp
    · by_cases hz : z = 0
      · subst z
        have hmix : coneMix lambda hlambda x 0 = coneScale lambda hlambda.1 x := by
          ext i
          simp [coneMix, coneScale]
        rw [hmix, hFhom x lambda hlambda.1, hFzero]
        simp
      · exact hpunctured x z hx hz lambda hlambda
  · intro hpunctured x z lambda hlambda
    by_cases hx : x = 0
    · subst x
      have hmix : coneMix lambda hlambda 0 z =
          coneScale (1 - lambda) (sub_nonneg.mpr hlambda.2) z := by
        ext i
        simp [coneMix, coneScale]
      rw [hmix, hFhom z (1 - lambda) (sub_nonneg.mpr hlambda.2), hFzero]
      simp
    · by_cases hz : z = 0
      · subst z
        have hmix : coneMix lambda hlambda x 0 = coneScale lambda hlambda.1 x := by
          ext i
          simp [coneMix, coneScale]
        rw [hmix, hFhom x lambda hlambda.1, hFzero]
        simp
      · exact hpunctured x z hx hz lambda hlambda

/-- The coordinatewise nonnegative cone with its origin removed is convex. -/
theorem puncturedConeConvex (I : Type u) :
    Convex ℝ {x : I → ℝ | Nonneg x ∧ x ≠ 0} := by
  intro x hx z hz a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hz.1 i))
  · intro hzero
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by simpa [ha0] using hab
      apply hz.2
      simpa [ha0, hb1] using hzero
    · apply hx.2
      funext i
      have hi : a * x i + b * z i = 0 := by
        simpa using congrFun hzero i
      have hbz : 0 ≤ b * z i := mul_nonneg hb (hz.1 i)
      have haxle : a * x i ≤ 0 := by
        calc
          a * x i ≤ a * x i + b * z i := le_add_of_nonneg_right hbz
          _ = 0 := hi
      have haxzero : a * x i = 0 :=
        le_antisymm haxle (mul_nonneg ha (hx.1 i))
      exact (mul_eq_zero.mp haxzero).resolve_left ha0

/-- Coordinatewise monotone composition preserves concavity; mixed
coordinate monotonicity preserves convexity with the corresponding coordinate
curvatures. -/
theorem compositionRule {V : Type v} [TopologicalSpace V] [AddCommGroup V]
    [Module ℝ V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    (C : Set V) (hC : Convex ℝ C) (m : ℕ) (U : Set (Fin m → ℝ))
    (hU : Convex ℝ U) (G : V → Fin m → ℝ) (hG : MapsTo G C U)
    (F : (Fin m → ℝ) → ℝ) :
    ((ConcaveOn ℝ U F ∧
        (∀ a ∈ U, ∀ b ∈ U, (∀ j, a j ≤ b j) → F a ≤ F b) ∧
        (∀ j : Fin m, ConcaveOn ℝ C (fun x => G x j))) →
      ConcaveOn ℝ C (F ∘ G)) ∧
    (∀ Ipos Ineg : Finset (Fin m), Disjoint Ipos Ineg →
      Ipos ∪ Ineg = Finset.univ →
      ConvexOn ℝ U F →
      (∀ a ∈ U, ∀ b ∈ U,
        (∀ j ∈ Ipos, a j ≤ b j) →
        (∀ j ∈ Ineg, b j ≤ a j) → F a ≤ F b) →
      (∀ j ∈ Ipos, ConvexOn ℝ C (fun x => G x j)) →
      (∀ j ∈ Ineg, ConcaveOn ℝ C (fun x => G x j)) →
      ConvexOn ℝ C (F ∘ G)) := by
  constructor
  · rintro ⟨hFconcave, hFmono, hGconcave⟩
    refine ⟨hC, ?_⟩
    intro x hx z hz a b ha hb hab
    have hxU : G x ∈ U := hG hx
    have hzU : G z ∈ U := hG hz
    have hwC : a • x + b • z ∈ C := hC hx hz ha hb hab
    have hwU : G (a • x + b • z) ∈ U := hG hwC
    have hvU : a • G x + b • G z ∈ U := hU hxU hzU ha hb hab
    have hinner : F (a • G x + b • G z) ≤ F (G (a • x + b • z)) :=
      hFmono (a • G x + b • G z) hvU (G (a • x + b • z)) hwU (fun j => by
        simpa using (hGconcave j).2 hx hz ha hb hab)
    have houter := hFconcave.2 hxU hzU ha hb hab
    simpa [Function.comp_apply] using houter.trans hinner
  · intro Ipos Ineg _hdisjoint _hcover hFconvex hFmono hGconvex hGconcave
    refine ⟨hC, ?_⟩
    intro x hx z hz a b ha hb hab
    have hxU : G x ∈ U := hG hx
    have hzU : G z ∈ U := hG hz
    have hwC : a • x + b • z ∈ C := hC hx hz ha hb hab
    have hwU : G (a • x + b • z) ∈ U := hG hwC
    have hvU : a • G x + b • G z ∈ U := hU hxU hzU ha hb hab
    have hinner : F (G (a • x + b • z)) ≤ F (a • G x + b • G z) :=
      hFmono (G (a • x + b • z)) hwU (a • G x + b • G z) hvU
        (fun j hj => by simpa using (hGconvex j hj).2 hx hz ha hb hab)
        (fun j hj => by simpa using (hGconcave j hj).2 hx hz ha hb hab)
    have houter := hFconvex.2 hxU hzU ha hb hab
    simpa [Function.comp_apply] using hinner.trans houter

/-- The pointwise monotone-composition argument specialized to one chord of
the punctured proof-carrying cone. -/
theorem coneCompositionRule {I : Type u} [Nonempty I]
    (m : ℕ) (G : ConeVec I → Fin m → ℝ) (U : Set (Fin m → ℝ))
    (F : (Fin m → ℝ) → ℝ) (hU : Convex ℝ U)
    (hG : ∀ q : ConeVec I, q ≠ 0 → G q ∈ U)
    (x z : ConeVec I) (hx : x ≠ 0) (hz : z ≠ 0)
    (lambda : ℝ) (hlambda : lambda ∈ Icc (0 : ℝ) 1)
    (hw : coneMix lambda hlambda x z ≠ 0) :
    ((ConcaveOn ℝ U F ∧
        (∀ a ∈ U, ∀ b ∈ U, (∀ j : Fin m, a j ≤ b j) → F a ≤ F b) ∧
        (∀ j : Fin m,
          lambda * G x j + (1 - lambda) * G z j ≤
            G (coneMix lambda hlambda x z) j)) →
      lambda * F (G x) + (1 - lambda) * F (G z) ≤
        F (G (coneMix lambda hlambda x z))) ∧
    (∀ Ipos Ineg : Finset (Fin m), Disjoint Ipos Ineg →
      Ipos ∪ Ineg = Finset.univ →
      ConvexOn ℝ U F →
      (∀ a ∈ U, ∀ b ∈ U,
        (∀ j ∈ Ipos, a j ≤ b j) →
        (∀ j ∈ Ineg, b j ≤ a j) → F a ≤ F b) →
      (∀ j ∈ Ipos,
        G (coneMix lambda hlambda x z) j ≤
          lambda * G x j + (1 - lambda) * G z j) →
      (∀ j ∈ Ineg,
        lambda * G x j + (1 - lambda) * G z j ≤
          G (coneMix lambda hlambda x z) j) →
      F (G (coneMix lambda hlambda x z)) ≤
        lambda * F (G x) + (1 - lambda) * F (G z)) := by
  have hxU : G x ∈ U := hG x hx
  have hzU : G z ∈ U := hG z hz
  have hwU : G (coneMix lambda hlambda x z) ∈ U := hG _ hw
  have hcoeff : lambda + (1 - lambda) = 1 :=
    (add_sub_assoc lambda 1 lambda).symm.trans (add_sub_cancel_left lambda 1)
  have hvU : lambda • G x + (1 - lambda) • G z ∈ U :=
    hU hxU hzU hlambda.1 (sub_nonneg.mpr hlambda.2) hcoeff
  constructor
  · rintro ⟨hFconcave, hFmono, hcoord⟩
    have hinner : F (lambda • G x + (1 - lambda) • G z) ≤
        F (G (coneMix lambda hlambda x z)) :=
      hFmono (lambda • G x + (1 - lambda) • G z) hvU
        (G (coneMix lambda hlambda x z)) hwU (fun j => by
          simpa using hcoord j)
    have houter :=
      hFconcave.2 hxU hzU hlambda.1 (sub_nonneg.mpr hlambda.2) hcoeff
    simpa using houter.trans hinner
  · intro Ipos Ineg _hdisjoint _hcover hFconvex hFmono hcoordPos hcoordNeg
    have hinner : F (G (coneMix lambda hlambda x z)) ≤
        F (lambda • G x + (1 - lambda) • G z) :=
      hFmono (G (coneMix lambda hlambda x z)) hwU
        (lambda • G x + (1 - lambda) • G z) hvU
        (fun j hj => by simpa using hcoordPos j hj)
        (fun j hj => by simpa using hcoordNeg j hj)
    have houter :=
      hFconvex.2 hxU hzU hlambda.1 (sub_nonneg.mpr hlambda.2) hcoeff
    simpa using hinner.trans houter

end ConditionalEntropy
