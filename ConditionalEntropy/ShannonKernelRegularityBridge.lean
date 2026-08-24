import ConditionalEntropy.ShannonKernelBridges
import ConditionalEntropy.ShannonKernelRegularity

/-!
# Integrated regularity of the Shannon kernels

The pointwise linear and quadratic identities are integrated against the two
Jordan components of the signed parameter measure.  Compactness of `Param`
supplies integrability of every fixed coefficient kernel.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

private theorem continuous_shannonKernels_param
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) :
    Continuous (fun beta : Param ↦ shannonKOne theta n z beta) ∧
      Continuous (fun beta : Param ↦ shannonKTwo theta n z beta) := by
  letI := shannonIndexNonempty theta n
  let L := shannonLineData theta n z
  obtain ⟨epsilon0, hepsilon0, hfixed0⟩ :=
    exists_fixedMaxCoordinate_shannonLine theta n z
  let epsilon := epsilon0 / 2
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  have hsubset : Icc (-epsilon) epsilon ⊆ Ioo (-epsilon0) epsilon0 := by
    intro lambda hlambda
    constructor
    · calc
        -epsilon0 < -(epsilon0 / 2) := by linarith
        _ ≤ lambda := by simpa only [epsilon] using hlambda.1
    · calc
        lambda ≤ epsilon0 / 2 := by simpa only [epsilon] using hlambda.2
        _ < epsilon0 := by linarith
  have hfixed : FixedMaxCoordinate L (Icc (-epsilon) epsilon)
      (shannonRepresentative theta n 2) := by
    intro lambda hlambda
    exact hfixed0 lambda (hsubset hlambda)
  have hpos : ∀ lambda ∈ Icc (-epsilon) epsilon, LinePositive L lambda := by
    intro lambda hlambda
    exact (hfixed lambda hlambda).1
  have hbundle := continuousOn_entropyLine_full_bundle L hepsilon hpos hfixed
  have hzero : (0 : ℝ) ∈ Icc (-epsilon) epsilon := by
    constructor <;> linarith
  have hsectionOne : Continuous
      (fun beta : Param ↦ entropyLineFirst L beta 0) := by
    rw [← continuousOn_univ]
    apply hbundle.2.1.comp
      (continuous_id.prodMk continuous_const).continuousOn
    intro beta _hbeta
    exact ⟨Set.mem_univ beta, hzero⟩
  have hsectionTwo : Continuous
      (fun beta : Param ↦ entropyLineSecond L beta 0) := by
    rw [← continuousOn_univ]
    apply hbundle.2.2.comp
      (continuous_id.prodMk continuous_const).continuousOn
    intro beta _hbeta
    exact ⟨Set.mem_univ beta, hzero⟩
  simpa only [shannonKOne, shannonKTwo, L] using
    And.intro hsectionOne hsectionTwo

private theorem integrable_continuous_param (nu : Measure Param)
    [IsFiniteMeasure nu] {f : Param → ℝ} (hf : Continuous f) :
    Integrable f nu := by
  have hcompact : IntegrableOn f Set.univ nu :=
    hf.continuousOn.integrableOn_compact isCompact_univ
  simpa [IntegrableOn] using hcompact

private theorem signedIntegral_sub_of_integrable_param
    (mu : SignedMeasure Param) {f g : Param → ℝ}
    (hfpos : Integrable f (signedPos mu))
    (hfneg : Integrable f (signedNeg mu))
    (hgpos : Integrable g (signedPos mu))
    (hgneg : Integrable g (signedNeg mu)) :
    signedIntegral mu (fun beta ↦ f beta - g beta) =
      signedIntegral mu f - signedIntegral mu g := by
  unfold signedIntegral
  rw [integral_sub hfpos hgpos, integral_sub hfneg hgneg]
  ring

private theorem signedIntegral_linear_combination_three
    (mu : SignedMeasure Param) (a b c : ℝ) (f g h : Param → ℝ)
    (hfpos : Integrable f (signedPos mu))
    (hfneg : Integrable f (signedNeg mu))
    (hgpos : Integrable g (signedPos mu))
    (hgneg : Integrable g (signedNeg mu))
    (hhpos : Integrable h (signedPos mu))
    (hhneg : Integrable h (signedNeg mu)) :
    signedIntegral mu (fun beta ↦ a * f beta + b * g beta + c * h beta) =
      a * signedIntegral mu f + b * signedIntegral mu g +
        c * signedIntegral mu h := by
  have hafpos : Integrable (fun beta ↦ a * f beta) (signedPos mu) :=
    hfpos.const_mul a
  have hafneg : Integrable (fun beta ↦ a * f beta) (signedNeg mu) :=
    hfneg.const_mul a
  have hbgpos : Integrable (fun beta ↦ b * g beta) (signedPos mu) :=
    hgpos.const_mul b
  have hbgneg : Integrable (fun beta ↦ b * g beta) (signedNeg mu) :=
    hgneg.const_mul b
  have hchpos : Integrable (fun beta ↦ c * h beta) (signedPos mu) :=
    hhpos.const_mul c
  have hchneg : Integrable (fun beta ↦ c * h beta) (signedNeg mu) :=
    hhneg.const_mul c
  calc
    signedIntegral mu (fun beta ↦ a * f beta + b * g beta + c * h beta) =
        signedIntegral mu (fun beta ↦
          a * f beta + (b * g beta + c * h beta)) := by
      apply signedIntegral_congr_ae
      exact ae_of_all (signedTV mu) fun beta ↦ by ring
    _ =
        signedIntegral mu (fun beta ↦ a * f beta) +
          signedIntegral mu (fun beta ↦ b * g beta + c * h beta) := by
      exact signedIntegral_add mu hafpos hafneg
        (hbgpos.add hchpos) (hbgneg.add hchneg)
    _ = signedIntegral mu (fun beta ↦ a * f beta) +
        (signedIntegral mu (fun beta ↦ b * g beta) +
          signedIntegral mu (fun beta ↦ c * h beta)) := by
      rw [signedIntegral_add mu hbgpos hbgneg hchpos hchneg]
    _ = _ := by
      rw [signedIntegral_smul, signedIntegral_smul, signedIntegral_smul]
      ring

theorem shannonGKernel_one_add (mu : SignedMeasure Param)
    (theta : ShannonData) (n : ℕ) (z w : ℝ × ℝ) :
    shannonGKernel mu theta n (z + w) 1 =
      shannonGKernel mu theta n z 1 + shannonGKernel mu theta n w 1 := by
  have hzcont := (continuous_shannonKernels_param theta n z).1
  have hwcont := (continuous_shannonKernels_param theta n w).1
  have hzpos := integrable_continuous_param (signedPos mu) hzcont
  have hzneg := integrable_continuous_param (signedNeg mu) hzcont
  have hwpos := integrable_continuous_param (signedPos mu) hwcont
  have hwneg := integrable_continuous_param (signedNeg mu) hwcont
  rw [(shannonKernelIntegralBridge mu theta n (z + w)).1,
    (shannonKernelIntegralBridge mu theta n z).1,
    (shannonKernelIntegralBridge mu theta n w).1]
  calc
    signedIntegral mu (fun beta ↦ shannonKOne theta n (z + w) beta) =
        signedIntegral mu (fun beta ↦
          shannonKOne theta n z beta + shannonKOne theta n w beta) := by
      apply signedIntegral_congr_ae
      exact ae_of_all (signedTV mu) fun beta ↦ shannonKOne_add theta n z w beta
    _ = _ := signedIntegral_add mu hzpos hzneg hwpos hwneg

theorem shannonGKernel_one_smul (mu : SignedMeasure Param)
    (theta : ShannonData) (n : ℕ) (c : ℝ) (z : ℝ × ℝ) :
    shannonGKernel mu theta n (c • z) 1 =
      c * shannonGKernel mu theta n z 1 := by
  rw [(shannonKernelIntegralBridge mu theta n (c • z)).1,
    (shannonKernelIntegralBridge mu theta n z).1]
  calc
    signedIntegral mu (fun beta ↦ shannonKOne theta n (c • z) beta) =
        signedIntegral mu (fun beta ↦ c * shannonKOne theta n z beta) := by
      apply signedIntegral_congr_ae
      exact ae_of_all (signedTV mu) fun beta ↦ shannonKOne_smul theta n c z beta
    _ = _ := signedIntegral_smul mu c _

theorem shannonGKernel_one_basis (mu : SignedMeasure Param)
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) :
    shannonGKernel mu theta n z 1 =
      z.1 * shannonGKernel mu theta n shannonBasisOne 1 +
        z.2 * shannonGKernel mu theta n shannonBasisTwo 1 := by
  conv_lhs => rw [shannonBasisDecomposition z]
  rw [shannonGKernel_one_add, shannonGKernel_one_smul,
    shannonGKernel_one_smul]

theorem continuous_shannonGKernel_one (mu : SignedMeasure Param)
    (theta : ShannonData) (n : ℕ) :
    Continuous (fun z : ℝ × ℝ ↦ shannonGKernel mu theta n z 1) := by
  have heq : (fun z : ℝ × ℝ ↦ shannonGKernel mu theta n z 1) =
      fun z ↦ z.1 * shannonGKernel mu theta n shannonBasisOne 1 +
        z.2 * shannonGKernel mu theta n shannonBasisTwo 1 := by
    funext z
    exact shannonGKernel_one_basis mu theta n z
  rw [heq]
  fun_prop

theorem shannonGKernel_two_basis (mu : SignedMeasure Param)
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) :
    shannonGKernel mu theta n z 2 =
      z.1 ^ 2 * shannonGKernel mu theta n shannonBasisOne 2 +
      z.1 * z.2 *
        (shannonGKernel mu theta n (shannonBasisOne + shannonBasisTwo) 2 -
          shannonGKernel mu theta n shannonBasisOne 2 -
          shannonGKernel mu theta n shannonBasisTwo 2) +
      z.2 ^ 2 * shannonGKernel mu theta n shannonBasisTwo 2 := by
  let f : Param → ℝ := fun beta ↦ shannonKTwo theta n shannonBasisOne beta
  let g : Param → ℝ := fun beta ↦
    shannonKTwo theta n (shannonBasisOne + shannonBasisTwo) beta -
      shannonKTwo theta n shannonBasisOne beta -
      shannonKTwo theta n shannonBasisTwo beta
  let h : Param → ℝ := fun beta ↦ shannonKTwo theta n shannonBasisTwo beta
  have hfcont := (continuous_shannonKernels_param theta n shannonBasisOne).2
  have hecont :=
    (continuous_shannonKernels_param theta n
      (shannonBasisOne + shannonBasisTwo)).2
  have hhcont := (continuous_shannonKernels_param theta n shannonBasisTwo).2
  have hgcont : Continuous g := by
    dsimp only [g]
    exact (hecont.sub hfcont).sub hhcont
  have hfpos : Integrable f (signedPos mu) :=
    integrable_continuous_param (signedPos mu) hfcont
  have hfneg : Integrable f (signedNeg mu) :=
    integrable_continuous_param (signedNeg mu) hfcont
  have hgpos : Integrable g (signedPos mu) :=
    integrable_continuous_param (signedPos mu) hgcont
  have hgneg : Integrable g (signedNeg mu) :=
    integrable_continuous_param (signedNeg mu) hgcont
  have hhpos : Integrable h (signedPos mu) :=
    integrable_continuous_param (signedPos mu) hhcont
  have hhneg : Integrable h (signedNeg mu) :=
    integrable_continuous_param (signedNeg mu) hhcont
  rw [(shannonKernelIntegralBridge mu theta n z).2.1]
  calc
    signedIntegral mu (fun beta ↦ shannonKTwo theta n z beta) =
        signedIntegral mu (fun beta ↦ z.1 ^ 2 * f beta +
          (z.1 * z.2) * g beta + z.2 ^ 2 * h beta) := by
      apply signedIntegral_congr_ae
      exact ae_of_all (signedTV mu) fun beta ↦
        shannonKTwo_basis_decomposition theta n z beta
    _ = z.1 ^ 2 * signedIntegral mu f +
        (z.1 * z.2) * signedIntegral mu g +
          z.2 ^ 2 * signedIntegral mu h :=
      signedIntegral_linear_combination_three mu _ _ _ _ _ _
        hfpos hfneg hgpos hgneg hhpos hhneg
    _ = _ := by
      dsimp only [f, g, h]
      have hepos : Integrable
          (fun beta ↦ shannonKTwo theta n
            (shannonBasisOne + shannonBasisTwo) beta) (signedPos mu) :=
        integrable_continuous_param (signedPos mu) hecont
      have heneg : Integrable
          (fun beta ↦ shannonKTwo theta n
            (shannonBasisOne + shannonBasisTwo) beta) (signedNeg mu) :=
        integrable_continuous_param (signedNeg mu) hecont
      have hsub1 : signedIntegral mu (fun beta ↦
          shannonKTwo theta n (shannonBasisOne + shannonBasisTwo) beta -
            shannonKTwo theta n shannonBasisOne beta) =
          signedIntegral mu (fun beta ↦
            shannonKTwo theta n (shannonBasisOne + shannonBasisTwo) beta) -
          signedIntegral mu (fun beta ↦
            shannonKTwo theta n shannonBasisOne beta) := by
        exact signedIntegral_sub_of_integrable_param mu
          hepos heneg hfpos hfneg
      have hsub2 : signedIntegral mu (fun beta ↦
          (shannonKTwo theta n (shannonBasisOne + shannonBasisTwo) beta -
            shannonKTwo theta n shannonBasisOne beta) -
              shannonKTwo theta n shannonBasisTwo beta) =
          signedIntegral mu (fun beta ↦
            shannonKTwo theta n (shannonBasisOne + shannonBasisTwo) beta -
              shannonKTwo theta n shannonBasisOne beta) -
          signedIntegral mu (fun beta ↦
            shannonKTwo theta n shannonBasisTwo beta) := by
        exact signedIntegral_sub_of_integrable_param mu
          (hepos.sub hfpos) (heneg.sub hfneg) hhpos hhneg
      rw [hsub2, hsub1,
        ← (shannonKernelIntegralBridge mu theta n shannonBasisOne).2.1,
        ← (shannonKernelIntegralBridge mu theta n shannonBasisTwo).2.1,
        ← (shannonKernelIntegralBridge mu theta n
          (shannonBasisOne + shannonBasisTwo)).2.1]

theorem continuous_shannonGKernel_two (mu : SignedMeasure Param)
    (theta : ShannonData) (n : ℕ) :
    Continuous (fun z : ℝ × ℝ ↦ shannonGKernel mu theta n z 2) := by
  have heq : (fun z : ℝ × ℝ ↦ shannonGKernel mu theta n z 2) =
      fun z ↦ z.1 ^ 2 * shannonGKernel mu theta n shannonBasisOne 2 +
        z.1 * z.2 *
          (shannonGKernel mu theta n (shannonBasisOne + shannonBasisTwo) 2 -
            shannonGKernel mu theta n shannonBasisOne 2 -
            shannonGKernel mu theta n shannonBasisTwo 2) +
        z.2 ^ 2 * shannonGKernel mu theta n shannonBasisTwo 2 := by
    funext z
    exact shannonGKernel_two_basis mu theta n z
  rw [heq]
  fun_prop

/-- Literal linearity and continuity conjunction for the integrated Shannon
kernels. -/
theorem shannonKernelRegularity (mu : SignedMeasure Param)
    (theta : ShannonData) (n : ℕ) :
    (∀ z w : ℝ × ℝ,
      shannonGKernel mu theta n (z + w) 1 =
        shannonGKernel mu theta n z 1 + shannonGKernel mu theta n w 1) ∧
    (∀ c : ℝ, ∀ z : ℝ × ℝ,
      shannonGKernel mu theta n (c • z) 1 =
        c * shannonGKernel mu theta n z 1) ∧
    Continuous (fun z : ℝ × ℝ ↦ shannonGKernel mu theta n z 1) ∧
    Continuous (fun z : ℝ × ℝ ↦ shannonGKernel mu theta n z 2) := by
  exact ⟨shannonGKernel_one_add mu theta n,
    shannonGKernel_one_smul mu theta n,
    continuous_shannonGKernel_one mu theta n,
    continuous_shannonGKernel_two mu theta n⟩

end ConditionalEntropy
