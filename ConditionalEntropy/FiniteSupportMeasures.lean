import ConditionalEntropy.Moments
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Finite-support probability measures

This module enumerates a finite probability support and records its exact
atomic decomposition, including the real and extended-real integral formulas
used by the finite-support reduction.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators

namespace ConditionalEntropy

/-- The raw point mass used by the project is the standard Dirac measure. -/
@[simp] theorem diracRaw_eq_dirac (a : Param) :
    diracRaw a = Measure.dirac a := by
  rfl

/-! ## Enumeration -/

/-- Exact dependent enumeration of a finite probability support. -/
theorem finiteSupportEnumeration (tau : ProbabilityMeasure Param)
    (hfin : (suppMeasure (probMeasure tau)).Finite) :
    ∃ (N : ℕ) (_hN : 0 < N) (alpha : Fin N → Param),
      Function.Injective alpha ∧
        Set.range alpha = suppMeasure (probMeasure tau) := by
  let mu : Measure Param := probMeasure tau
  have hmuOne : mu Set.univ = 1 := by
    simp [mu, probMeasure]
  have hmuNe : mu ≠ 0 := by
    intro hzero
    rw [hzero] at hmuOne
    simp at hmuOne
  have hsuppNe : (suppMeasure mu).Nonempty := by
    simpa only [suppMeasure] using Measure.nonempty_support hmuNe
  letI : Fintype {a // a ∈ suppMeasure mu} := hfin.fintype
  let N := Fintype.card {a // a ∈ suppMeasure mu}
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨⟨hsuppNe.some, hsuppNe.some_mem⟩⟩
  let e : Fin N ≃ {a // a ∈ suppMeasure mu} :=
    (Fintype.equivFin {a // a ∈ suppMeasure mu}).symm
  let alpha : Fin N → Param := fun i => (e i).1
  refine ⟨N, hN, alpha, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    exact Subtype.ext hij
  · ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro ha
      let x : {a // a ∈ suppMeasure mu} := ⟨a, ha⟩
      exact ⟨e.symm x, by simp [alpha, x]⟩

/-! ## Atomic decomposition -/

/-- A point in a finite support has strictly positive singleton mass. -/
theorem finiteSupport_singleton_pos {N : ℕ} (alpha : Fin N → Param)
    (mu : Measure Param) (hsupp : suppMeasure mu = Set.range alpha)
    (i : Fin N) :
    0 < mu ({alpha i} : Set Param) := by
  let T : Set Param := Set.range alpha \ {alpha i}
  let U : Set Param := Tᶜ
  have hTfin : T.Finite := (Set.finite_range alpha).sdiff
  have hUopen : IsOpen U := hTfin.isClosed.isOpen_compl
  have hiU : alpha i ∈ U := by
    intro hiT
    exact hiT.2 rfl
  have hiSupp : alpha i ∈ suppMeasure mu := by
    rw [hsupp]
    exact Set.mem_range_self i
  have hUpos : 0 < mu U := by
    rw [suppMeasure, Measure.support_eq_forall_isOpen] at hiSupp
    exact hiSupp U hiU hUopen
  have hUcap : U ∩ suppMeasure mu = ({alpha i} : Set Param) := by
    rw [hsupp]
    ext x
    constructor
    · rintro ⟨hxU, ⟨j, hj⟩⟩
      have hxi : x = alpha i := by
        by_contra hne
        exact hxU ⟨⟨j, hj⟩, hne⟩
      simpa only [Set.mem_singleton_iff] using hxi
    · intro hxi
      have hxi' : x = alpha i := Set.mem_singleton_iff.mp hxi
      subst x
      refine ⟨?_, Set.mem_range_self i⟩
      intro hiT
      exact hiT.2 rfl
  have hinter : mu (suppMeasure mu ∩ U) = mu U := by
    apply Measure.measure_inter_eq_of_ae
    change ∀ᵐ a ∂mu, a ∈ mu.support
    exact Measure.support_mem_ae
  have hatom : mu ({alpha i} : Set Param) = mu U := by
    rw [← hUcap, Set.inter_comm]
    exact hinter
  rwa [hatom]

/-- Exact finite-support Dirac decomposition and both integral formulas. -/
theorem finiteSupportDirac (N : ℕ) (_hN : 0 < N)
    (alpha : Fin N → Param) (halpha : Function.Injective alpha)
    (tau : ProbabilityMeasure Param)
    (hsupp : suppMeasure (probMeasure tau) = Set.range alpha) :
    let m : Fin N → ENNReal := fun ell =>
      probMeasure tau ({alpha ell} : Set Param)
    let w : Fin N → ℝ := fun ell => ENNReal.toReal (m ell)
    (∀ ell : Fin N, m ell ≠ ⊤) ∧
      (∀ ell : Fin N, 0 < m ell) ∧
      (∀ ell : Fin N, 0 < w ell) ∧
      (∑ ell : Fin N, w ell) = 1 ∧
      probMeasure tau =
        ∑ ell : Fin N, m ell • diracRaw (alpha ell) ∧
      (∀ f : Param → ℝ, Measurable f →
        (∃ C : ℝ, ∀ a, |f a| ≤ C) →
        ∫ a, f a ∂(probMeasure tau) =
          ∑ ell : Fin N, w ell * f (alpha ell)) ∧
      (∀ g : Param → ENNReal, Measurable g →
        ∫⁻ a, g a ∂(probMeasure tau) =
          ∑ ell : Fin N, m ell * g (alpha ell)) := by
  let m : Fin N → ENNReal := fun ell =>
    probMeasure tau ({alpha ell} : Set Param)
  let w : Fin N → ℝ := fun ell => ENNReal.toReal (m ell)
  have hmTop : ∀ ell : Fin N, m ell ≠ (⊤ : ENNReal) := by
    intro ell
    exact ne_of_lt <| lt_of_le_of_lt
      (measure_mono (Set.subset_univ ({alpha ell} : Set Param))) <| by
        simp [probMeasure]
  have hmPos : ∀ ell : Fin N, 0 < m ell := by
    intro ell
    exact finiteSupport_singleton_pos alpha (probMeasure tau) hsupp ell
  have hwPos : ∀ ell : Fin N, 0 < w ell := by
    intro ell
    exact ENNReal.toReal_pos (hmPos ell).ne' (hmTop ell)
  let s : Finset Param := Finset.univ.image alpha
  have hsSet : (↑s : Set Param) = suppMeasure (probMeasure tau) := by
    ext a
    simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rw [hsupp]
  have hae : ∀ᵐ a ∂(probMeasure tau), a ∈ s := by
    have hsuppAE := Measure.support_mem_ae (μ := probMeasure tau)
    filter_upwards [hsuppAE] with a ha
    change a ∈ (↑s : Set Param)
    rw [hsSet]
    exact ha
  have hdiracStd : probMeasure tau =
      ∑ ell : Fin N, m ell • Measure.dirac (alpha ell) := by
    have hfin := (Measure.ae_mem_finset_iff (μ := probMeasure tau) (s := s)).mp hae
    rw [show s = Finset.univ.image alpha by rfl] at hfin
    rw [Finset.sum_image] at hfin
    · simpa only [m] using hfin
    · exact halpha.injOn
  have hdirac : probMeasure tau =
      ∑ ell : Fin N, m ell • diracRaw (alpha ell) := by
    simpa only [diracRaw_eq_dirac] using hdiracStd
  have hmSum : (∑ ell : Fin N, m ell) = 1 := by
    calc
      (∑ ell : Fin N, m ell) =
          (∑ ell : Fin N, m ell • diracRaw (alpha ell)) Set.univ := by
            simp [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
      _ = probMeasure tau Set.univ :=
        congrArg (fun nu : Measure Param => nu Set.univ) hdirac.symm
      _ = 1 := by simp [probMeasure]
  have hwSum : (∑ ell : Fin N, w ell) = 1 := by
    calc
      (∑ ell : Fin N, w ell) = ENNReal.toReal (∑ ell : Fin N, m ell) := by
        exact (ENNReal.toReal_sum (fun ell _hell => hmTop ell)).symm
      _ = 1 := by rw [hmSum]; simp
  refine ⟨hmTop, hmPos, hwPos, hwSum, hdirac, ?_, ?_⟩
  · intro f _hf _hbound
    calc
      ∫ a, f a ∂(probMeasure tau) =
          ∫ a, f a ∂(∑ ell : Fin N, m ell • Measure.dirac (alpha ell)) :=
        congrArg (fun nu : Measure Param => ∫ a, f a ∂nu) hdiracStd
      _ = ∑ ell : Fin N,
          ∫ a, f a ∂(m ell • Measure.dirac (alpha ell)) := by
        apply integral_finsetSum_measure
        intro ell _hell
        exact (integrable_dirac (by simp)).smul_measure (hmTop ell)
      _ = ∑ ell : Fin N, w ell * f (alpha ell) := by
        simp only [integral_smul_measure, integral_dirac, w, smul_eq_mul]
  · intro g hg
    calc
      ∫⁻ a, g a ∂(probMeasure tau) =
          ∫⁻ a, g a ∂(∑ ell : Fin N, m ell • diracRaw (alpha ell)) :=
        congrArg (fun nu : Measure Param => ∫⁻ a, g a ∂nu) hdirac
      _ = ∑ ell : Fin N, ∫⁻ a, g a ∂(m ell • diracRaw (alpha ell)) :=
        lintegral_finsetSum_measure _ _ _
      _ = ∑ ell : Fin N, m ell * g (alpha ell) := by
        simp only [lintegral_smul_measure, diracRaw_eq_dirac,
          lintegral_dirac (f := g), smul_eq_mul]

end ConditionalEntropy
