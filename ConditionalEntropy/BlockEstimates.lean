import ConditionalEntropy.BlockData
import ConditionalEntropy.EndpointLineCalculus
import ConditionalEntropy.FiniteExtrema
import Mathlib.Order.Filter.Finite

/-!
# Quantitative estimates for finite block families

This module differentiates the rounded block escorts in the Rényi order and
packages the uniform estimates used by the dominant-block localization
arguments.  The carrier and all non-derivative estimates live in
`BlockData`; this file adds no assumptions to those definitions.
-/

noncomputable section

open Filter Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

/-- The logarithmic slope of one block contribution as a function of order. -/
def blockOrderSlope {J : ℕ} (B : BlockData J) (n : ℕ)
    (j : Fin (J + 1)) : ℝ :=
  B.a j * Real.log (blockScale n)

/-- The positive partition function normalizing block escorts. -/
def blockPartition {J : ℕ} (B : BlockData J) (n : ℕ)
    (alpha : ℝ) : ℝ :=
  ∑ j, blockContribution B n j alpha

theorem blockPartition_pos {J : ℕ} (B : BlockData J) (n : ℕ)
    (alpha : ℝ) : 0 < blockPartition B n alpha :=
  sum_blockContribution_pos B n alpha

theorem log_blockScale_nonneg (n : ℕ) : 0 ≤ Real.log (blockScale n) :=
  Real.log_nonneg (one_le_blockScale n)

/-- Exact order derivative of one rounded block contribution. -/
theorem hasDerivAt_blockContribution {J : ℕ} (B : BlockData J) (n : ℕ)
    (j : Fin (J + 1)) (alpha : ℝ) :
    HasDerivAt (blockContribution B n j)
      (blockContribution B n j alpha * blockOrderSlope B n j) alpha := by
  let q : ℝ := Real.rpow (blockScale n) (B.a j)
  have hq : 0 < q := Real.rpow_pos_of_pos (blockScale_pos n) (B.a j)
  have hp := (hasDerivAt_id (x := alpha)).const_rpow hq
  have hmul := hp.const_mul (blockCount B n j : ℝ)
  have hlog : Real.log q = B.a j * Real.log (blockScale n) := by
    dsimp [q]
    rw [Real.log_rpow (blockScale_pos n)]
  rw [hlog] at hmul
  dsimp only [q] at hmul
  change HasDerivAt
    (fun y : ℝ ↦ (blockCount B n j : ℝ) *
      (Real.rpow (blockScale n) (B.a j)) ^ y)
    (((blockCount B n j : ℝ) *
        (Real.rpow (blockScale n) (B.a j)) ^ alpha) *
      (B.a j * Real.log (blockScale n))) alpha
  apply hmul.congr_deriv
  simp only [id_eq]
  ring

/-- Exact order derivative of the block partition function. -/
theorem hasDerivAt_blockPartition {J : ℕ} (B : BlockData J) (n : ℕ)
    (alpha : ℝ) :
    HasDerivAt (blockPartition B n)
      (∑ j, blockContribution B n j alpha * blockOrderSlope B n j) alpha := by
  classical
  unfold blockPartition
  apply HasDerivAt.fun_sum
  intro j _
  exact hasDerivAt_blockContribution B n j alpha

/-- A block escort mean is a ratio of the corresponding unnormalized
weighted contribution sum and the partition function. -/
theorem blockEscortMean_eq_ratio {J : ℕ} (B : BlockData J) (n : ℕ)
    (alpha : ℝ) (v : Fin (J + 1) → ℝ) :
    blockEscortMean B n alpha v =
      (∑ j, blockContribution B n j alpha * v j) /
        blockPartition B n alpha := by
  unfold blockEscortMean blockEscort
  calc
    ∑ j, (blockContribution B n j alpha /
        blockPartition B n alpha) * v j =
        ∑ j, (blockContribution B n j alpha * v j) /
          blockPartition B n alpha := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ j, blockContribution B n j alpha * v j) /
          blockPartition B n alpha := by
      rw [← Finset.sum_div]

/-- Exact softmax derivative of a block escort. -/
theorem hasDerivAt_blockEscort {J : ℕ} (B : BlockData J) (n : ℕ)
    (j : Fin (J + 1)) (alpha : ℝ) :
    HasDerivAt (blockEscort B n j)
      (Real.log (blockScale n) * blockEscort B n j alpha *
        (B.a j - blockEscortMean B n alpha B.a)) alpha := by
  have hnum := hasDerivAt_blockContribution B n j alpha
  have hden := hasDerivAt_blockPartition B n alpha
  have hden0 : blockPartition B n alpha ≠ 0 := (blockPartition_pos B n alpha).ne'
  have hquot := hnum.div hden hden0
  have hmean := blockEscortMean_eq_ratio B n alpha B.a
  have hlogsum :
      (∑ l, blockContribution B n l alpha * blockOrderSlope B n l) =
        Real.log (blockScale n) *
          (∑ l, blockContribution B n l alpha * B.a l) := by
    unfold blockOrderSlope
    calc
      ∑ l, blockContribution B n l alpha *
          (B.a l * Real.log (blockScale n)) =
          ∑ l, Real.log (blockScale n) *
            (blockContribution B n l alpha * B.a l) := by
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = Real.log (blockScale n) *
          (∑ l, blockContribution B n l alpha * B.a l) := by
        rw [Finset.mul_sum]
  have hquot' : HasDerivAt (blockEscort B n j)
      ((blockContribution B n j alpha * blockOrderSlope B n j *
          blockPartition B n alpha -
        blockContribution B n j alpha *
          (∑ l, blockContribution B n l alpha * blockOrderSlope B n l)) /
        blockPartition B n alpha ^ 2) alpha := by
    change HasDerivAt (blockContribution B n j / blockPartition B n)
      ((blockContribution B n j alpha * blockOrderSlope B n j *
          blockPartition B n alpha -
        blockContribution B n j alpha *
          (∑ l, blockContribution B n l alpha * blockOrderSlope B n l)) /
        blockPartition B n alpha ^ 2) alpha
    exact hquot
  apply hquot'.congr_deriv
  have hescort : blockEscort B n j alpha =
      blockContribution B n j alpha / blockPartition B n alpha := rfl
  rw [hescort, hmean, hlogsum, blockOrderSlope]
  field_simp [hden0]

theorem deriv_blockEscort {J : ℕ} (B : BlockData J) (n : ℕ)
    (j : Fin (J + 1)) (alpha : ℝ) :
    deriv (fun s ↦ blockEscort B n j s) alpha =
      Real.log (blockScale n) * blockEscort B n j alpha *
        (B.a j - blockEscortMean B n alpha B.a) :=
  (hasDerivAt_blockEscort B n j alpha).deriv

/-- A finite global bound for all amplitude differences. -/
def blockAmplitudeDiameter {J : ℕ} (B : BlockData J) : ℝ :=
  ∑ j, ∑ l, |B.a j - B.a l|

theorem blockAmplitudeDiameter_nonneg {J : ℕ} (B : BlockData J) :
    0 ≤ blockAmplitudeDiameter B := by
  exact Finset.sum_nonneg fun j _ ↦ Finset.sum_nonneg fun l _ ↦ abs_nonneg _

theorem abs_amplitude_sub_le_diameter {J : ℕ} (B : BlockData J)
    (j l : Fin (J + 1)) :
    |B.a j - B.a l| ≤ blockAmplitudeDiameter B := by
  have hinner : |B.a j - B.a l| ≤ ∑ r, |B.a j - B.a r| := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun r : Fin (J + 1) ↦ |B.a j - B.a r|)
      (fun r _ ↦ abs_nonneg _) (Finset.mem_univ l)
  have houter : (∑ r, |B.a j - B.a r|) ≤
      ∑ q, ∑ r, |B.a q - B.a r| := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun q : Fin (J + 1) ↦ ∑ r, |B.a q - B.a r|)
      (fun q _ ↦ Finset.sum_nonneg fun r _ ↦ abs_nonneg _)
      (Finset.mem_univ j)
  exact hinner.trans houter

theorem blockEscort_le_one {J : ℕ} (B : BlockData J) (n : ℕ)
    (j : Fin (J + 1)) (alpha : ℝ) :
    blockEscort B n j alpha ≤ 1 := by
  have hj : blockEscort B n j alpha ≤ ∑ l, blockEscort B n l alpha := by
    exact Finset.single_le_sum
      (fun l _ ↦ blockEscort_nonneg B n l alpha) (Finset.mem_univ j)
  simpa only [sum_blockEscort] using hj

theorem blockOutsideMass_le_one {J : ℕ} (B : BlockData J) (n : ℕ)
    (k : Fin (J + 1)) (alpha : ℝ) :
    ∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha ≤ 1 := by
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun j ↦ blockEscort B n j alpha) (Finset.mem_univ k)
  have hsum := sum_blockEscort B n alpha
  have hk := blockEscort_nonneg B n k alpha
  linarith

/-- Every amplitude differs from the escort amplitude mean by at most the
global finite diameter. -/
theorem abs_amplitude_sub_escortMean_le {J : ℕ} (B : BlockData J)
    (n : ℕ) (j : Fin (J + 1)) (alpha : ℝ) :
    |B.a j - blockEscortMean B n alpha B.a| ≤ blockAmplitudeDiameter B := by
  have hcenter := abs_blockEscortWeighted_sub_le_outside B n alpha j B.a
    (blockAmplitudeDiameter B) (fun l ↦ abs_amplitude_sub_le_diameter B l j)
  rw [abs_sub_comm] at hcenter
  calc
    |B.a j - blockEscortMean B n alpha B.a|
        ≤ blockAmplitudeDiameter B *
          (∑ l ∈ Finset.univ.erase j, blockEscort B n l alpha) := hcenter
    _ ≤ blockAmplitudeDiameter B * 1 :=
      mul_le_mul_of_nonneg_left (blockOutsideMass_le_one B n j alpha)
        (blockAmplitudeDiameter_nonneg B)
    _ = blockAmplitudeDiameter B := mul_one _

/-- At a designated block, the amplitude-centering error gains the outside
escort mass. -/
theorem abs_dominantAmplitude_sub_escortMean_le {J : ℕ} (B : BlockData J)
    (n : ℕ) (k : Fin (J + 1)) (alpha : ℝ) :
    |B.a k - blockEscortMean B n alpha B.a| ≤
      blockAmplitudeDiameter B *
        (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha) := by
  have hcenter := abs_blockEscortWeighted_sub_le_outside B n alpha k B.a
    (blockAmplitudeDiameter B) (fun l ↦ abs_amplitude_sub_le_diameter B l k)
  rw [abs_sub_comm]
  exact hcenter

/-- Absolute-value form of the exact escort derivative. -/
theorem abs_deriv_blockEscort {J : ℕ} (B : BlockData J) (n : ℕ)
    (j : Fin (J + 1)) (alpha : ℝ) :
    |deriv (fun s ↦ blockEscort B n j s) alpha| =
      Real.log (blockScale n) * blockEscort B n j alpha *
        |B.a j - blockEscortMean B n alpha B.a| := by
  rw [deriv_blockEscort, abs_mul, abs_mul,
    abs_of_nonneg (log_blockScale_nonneg n),
    abs_of_nonneg (blockEscort_nonneg B n j alpha)]

/-- The total order variation of all escorts is controlled by outside mass
whenever `k` is the designated dominant block. -/
theorem sum_abs_deriv_blockEscort_le_outside {J : ℕ} (B : BlockData J)
    (n : ℕ) (k : Fin (J + 1)) (alpha : ℝ) :
    ∑ j, |deriv (fun s ↦ blockEscort B n j s) alpha| ≤
      (2 * blockAmplitudeDiameter B) * Real.log (blockScale n) *
        (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha) := by
  let D := blockAmplitudeDiameter B
  let L := Real.log (blockScale n)
  let R := ∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha
  have hD : 0 ≤ D := blockAmplitudeDiameter_nonneg B
  have hL : 0 ≤ L := log_blockScale_nonneg n
  have hpK : 0 ≤ blockEscort B n k alpha := blockEscort_nonneg B n k alpha
  have hpK1 : blockEscort B n k alpha ≤ 1 := blockEscort_le_one B n k alpha
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact Finset.sum_nonneg fun j _ ↦ blockEscort_nonneg B n j alpha
  have hk : |deriv (fun s ↦ blockEscort B n k s) alpha| ≤ D * L * R := by
    rw [abs_deriv_blockEscort]
    have hc : |B.a k - blockEscortMean B n alpha B.a| ≤ D * R := by
      simpa only [D, R] using
        abs_dominantAmplitude_sub_escortMean_le B n k alpha
    have hLP : L * blockEscort B n k alpha ≤ L * 1 :=
      mul_le_mul_of_nonneg_left hpK1 hL
    calc
      L * blockEscort B n k alpha *
          |B.a k - blockEscortMean B n alpha B.a|
          ≤ (L * 1) * (D * R) :=
        mul_le_mul hLP hc (abs_nonneg _) (mul_nonneg hL (by norm_num))
      _ = D * L * R := by ring
  have hout :
      ∑ j ∈ Finset.univ.erase k,
          |deriv (fun s ↦ blockEscort B n j s) alpha| ≤ D * L * R := by
    calc
      ∑ j ∈ Finset.univ.erase k,
          |deriv (fun s ↦ blockEscort B n j s) alpha|
          ≤ ∑ j ∈ Finset.univ.erase k,
              (D * L) * blockEscort B n j alpha := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_deriv_blockEscort]
        have hc : |B.a j - blockEscortMean B n alpha B.a| ≤ D := by
          simpa only [D] using abs_amplitude_sub_escortMean_le B n j alpha
        have hLp : 0 ≤ L * blockEscort B n j alpha :=
          mul_nonneg hL (blockEscort_nonneg B n j alpha)
        calc
          L * blockEscort B n j alpha *
              |B.a j - blockEscortMean B n alpha B.a|
              ≤ L * blockEscort B n j alpha * D :=
            mul_le_mul_of_nonneg_left hc hLp
          _ = (D * L) * blockEscort B n j alpha := by ring
      _ = D * L * R := by
        dsimp only [R]
        rw [Finset.mul_sum]
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun j ↦ |deriv (fun s ↦ blockEscort B n j s) alpha|)
    (Finset.mem_univ k)
  calc
    ∑ j, |deriv (fun s ↦ blockEscort B n j s) alpha| =
        |deriv (fun s ↦ blockEscort B n k s) alpha| +
          ∑ j ∈ Finset.univ.erase k,
            |deriv (fun s ↦ blockEscort B n j s) alpha| := hsplit.symm
    _ ≤ D * L * R + D * L * R := add_le_add hk hout
    _ = (2 * blockAmplitudeDiameter B) * Real.log (blockScale n) *
        (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha) := by
      dsimp only [D, L, R]
      ring

/-- The two quantitative escort clauses in the dominant-block lemma, with
one constant uniform in scale and order. -/
theorem dominantBlockEscortEstimates {J : ℕ} (B : BlockData J)
    (I : Set ℝ) (k : Fin (J + 1)) (eta : ℝ) (_h_eta : 0 < eta)
    (hgap : ∀ alpha ∈ I, ∀ j : Fin (J + 1), j ≠ k →
      eta ≤ blockExponent B k alpha - blockExponent B j alpha) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (alpha : ℝ), alpha ∈ I →
        (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha ≤
          C * Real.rpow (blockScale n) (-eta)) ∧
        (∑ j, |deriv (fun s ↦ blockEscort B n j s) alpha| ≤
          C * Real.log (blockScale n) *
            Real.rpow (blockScale n) (-eta)) := by
  obtain ⟨C₀, hC₀, hout⟩ := dominantBlockOutsideMass B I k eta hgap
  let D := blockAmplitudeDiameter B
  let C := (1 + 2 * D) * C₀
  have hD : 0 ≤ D := blockAmplitudeDiameter_nonneg B
  have hfac : 0 ≤ 1 + 2 * D := by positivity
  have hC : 0 ≤ C := mul_nonneg hfac hC₀
  refine ⟨C, hC, ?_⟩
  intro n alpha h_alpha
  let r := Real.rpow (blockScale n) (-eta)
  let L := Real.log (blockScale n)
  have hr : 0 ≤ r := Real.rpow_nonneg (blockScale_pos n).le _
  have hL : 0 ≤ L := log_blockScale_nonneg n
  have hC₀C : C₀ ≤ C := by
    dsimp only [C]
    have hextra : 0 ≤ (2 * D) * C₀ :=
      mul_nonneg (mul_nonneg (by norm_num) hD) hC₀
    nlinarith
  constructor
  · calc
      ∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha
          ≤ C₀ * Real.rpow (blockScale n) (-eta) := hout n alpha h_alpha
      _ ≤ C * Real.rpow (blockScale n) (-eta) :=
        mul_le_mul_of_nonneg_right hC₀C hr
  · calc
      ∑ j, |deriv (fun s ↦ blockEscort B n j s) alpha|
          ≤ (2 * D) * L *
            (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha) := by
        simpa only [D, L] using sum_abs_deriv_blockEscort_le_outside B n k alpha
      _ ≤ (2 * D) * L * (C₀ * r) :=
        mul_le_mul_of_nonneg_left (hout n alpha h_alpha)
          (mul_nonneg (mul_nonneg (by positivity) hD) hL)
      _ ≤ C * L * r := by
        have hcoef : (2 * D) * C₀ ≤ C := by
          dsimp only [C]
          nlinarith [hC₀]
        nlinarith [mul_nonneg hL hr]
      _ = C * Real.log (blockScale n) *
          Real.rpow (blockScale n) (-eta) := rfl

/-- Exact order derivative of a blockwise escort average. -/
theorem hasDerivAt_blockEscortMean_order {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (alpha : ℝ) :
    HasDerivAt (fun s ↦ blockEscortMean B n s u)
      (∑ j, deriv (fun s ↦ blockEscort B n j s) alpha * u j) alpha := by
  classical
  unfold blockEscortMean
  apply HasDerivAt.fun_sum
  intro j _
  have hj := (hasDerivAt_blockEscort B n j alpha).mul_const (u j)
  apply hj.congr_deriv
  rw [deriv_blockEscort]

theorem deriv_blockEscortMean_order {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (alpha : ℝ) :
    deriv (fun s ↦ blockEscortMean B n s u) alpha =
      ∑ j, deriv (fun s ↦ blockEscort B n j s) alpha * u j :=
  (hasDerivAt_blockEscortMean_order B n u alpha).deriv

/-- Exact order derivative of a blockwise escort second moment. -/
theorem hasDerivAt_blockEscortSecond_order {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (alpha : ℝ) :
    HasDerivAt (fun s ↦ blockEscortSecond B n s u)
      (∑ j, deriv (fun s ↦ blockEscort B n j s) alpha * (u j) ^ 2) alpha := by
  classical
  unfold blockEscortSecond
  apply HasDerivAt.fun_sum
  intro j _
  have hj := (hasDerivAt_blockEscort B n j alpha).mul_const ((u j) ^ 2)
  apply hj.congr_deriv
  rw [deriv_blockEscort]

theorem deriv_blockEscortSecond_order {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (alpha : ℝ) :
    deriv (fun s ↦ blockEscortSecond B n s u) alpha =
      ∑ j, deriv (fun s ↦ blockEscort B n j s) alpha * (u j) ^ 2 :=
  (hasDerivAt_blockEscortSecond_order B n u alpha).deriv

/-- A bounded block statistic transfers the total escort variation to its
escort-average order derivative. -/
theorem abs_deriv_blockEscortMean_order_le {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (U alpha : ℝ)
    (_h_U : 0 ≤ U) (h_u : ∀ j, |u j| ≤ U) :
    |deriv (fun s ↦ blockEscortMean B n s u) alpha| ≤
      U * ∑ j, |deriv (fun s ↦ blockEscort B n j s) alpha| := by
  rw [deriv_blockEscortMean_order]
  calc
    |∑ j, deriv (fun s ↦ blockEscort B n j s) alpha * u j|
        ≤ ∑ j, |deriv (fun s ↦ blockEscort B n j s) alpha * u j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |deriv (fun s ↦ blockEscort B n j s) alpha| * U := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (h_u j) (abs_nonneg _)
    _ = U * ∑ j, |deriv (fun s ↦ blockEscort B n j s) alpha| := by
      rw [← Finset.sum_mul]
      ring

theorem abs_deriv_blockEscortSecond_order_le {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (U alpha : ℝ)
    (h_U : 0 ≤ U) (h_u : ∀ j, |u j| ≤ U) :
    |deriv (fun s ↦ blockEscortSecond B n s u) alpha| ≤
      U ^ 2 * ∑ j, |deriv (fun s ↦ blockEscort B n j s) alpha| := by
  rw [deriv_blockEscortSecond_order]
  calc
    |∑ j, deriv (fun s ↦ blockEscort B n j s) alpha * (u j) ^ 2|
        ≤ ∑ j,
          |deriv (fun s ↦ blockEscort B n j s) alpha * (u j) ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |deriv (fun s ↦ blockEscort B n j s) alpha| * U ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have habssq : |(u j) ^ 2| = (u j) ^ 2 := abs_of_nonneg (sq_nonneg _)
      rw [abs_mul, habssq]
      have hsq : (u j) ^ 2 ≤ U ^ 2 :=
        sq_le_sq.mpr (by simpa [abs_of_nonneg h_U] using h_u j)
      exact mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
    _ = U ^ 2 * ∑ j, |deriv (fun s ↦ blockEscort B n j s) alpha| := by
      rw [← Finset.sum_mul]
      ring

/-- Full dominant-block package: outside escort mass, total escort order
variation, the first two moment errors, variance, and the order derivatives
of both moments. -/
theorem dominantBlock {J : ℕ} (B : BlockData J) (I : Set ℝ)
    (k : Fin (J + 1)) (eta : ℝ) (h_eta : 0 < eta)
    (hgap : ∀ alpha ∈ I, ∀ j : Fin (J + 1), j ≠ k →
      eta ≤ blockExponent B k alpha - blockExponent B j alpha) :
    (∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (alpha : ℝ), alpha ∈ I →
        (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha ≤
          C * Real.rpow (blockScale n) (-eta)) ∧
        (∑ j, |deriv (fun s ↦ blockEscort B n j s) alpha| ≤
          C * Real.log (blockScale n) *
            Real.rpow (blockScale n) (-eta))) ∧
    (∀ U : ℝ, 0 ≤ U →
      ∃ C_U : ℝ, 0 ≤ C_U ∧
        ∀ (u : Fin (J + 1) → ℝ), (∀ j, |u j| ≤ U) →
          ∀ (n : ℕ) (alpha : ℝ), alpha ∈ I →
            (|blockEscortMean B n alpha u - u k| +
                |blockEscortSecond B n alpha u - (u k) ^ 2| +
                blockEscortVar B n alpha u ≤
              C_U * Real.rpow (blockScale n) (-eta)) ∧
            (|deriv (fun s ↦ blockEscortMean B n s u) alpha| +
                |deriv (fun s ↦ blockEscortSecond B n s u) alpha| ≤
              C_U * Real.log (blockScale n) *
                Real.rpow (blockScale n) (-eta))) := by
  obtain ⟨C, hC, hescort⟩ :=
    dominantBlockEscortEstimates B I k eta h_eta hgap
  refine ⟨⟨C, hC, hescort⟩, ?_⟩
  intro U hU
  obtain ⟨C_m, hC_m, hmom⟩ := dominantBlockMomentBounds B I k eta U hU hgap
  let C_d : ℝ := (U + U ^ 2) * C
  let C_U : ℝ := C_m + C_d
  have hUd : 0 ≤ U + U ^ 2 := add_nonneg hU (sq_nonneg U)
  have hC_d : 0 ≤ C_d := mul_nonneg hUd hC
  have hC_U : 0 ≤ C_U := add_nonneg hC_m hC_d
  refine ⟨C_U, hC_U, ?_⟩
  intro u hu n alpha h_alpha
  let r := Real.rpow (blockScale n) (-eta)
  let L := Real.log (blockScale n)
  let S := ∑ j, |deriv (fun s ↦ blockEscort B n j s) alpha|
  have hr : 0 ≤ r := Real.rpow_nonneg (blockScale_pos n).le _
  have hL : 0 ≤ L := log_blockScale_nonneg n
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hesc := hescort n alpha h_alpha
  have hmean := abs_deriv_blockEscortMean_order_le B n u U alpha hU hu
  have hsecond := abs_deriv_blockEscortSecond_order_le B n u U alpha hU hu
  constructor
  · calc
      |blockEscortMean B n alpha u - u k| +
          |blockEscortSecond B n alpha u - (u k) ^ 2| +
          blockEscortVar B n alpha u
          ≤ C_m * Real.rpow (blockScale n) (-eta) :=
        hmom u hu n alpha h_alpha
      _ ≤ C_U * Real.rpow (blockScale n) (-eta) := by
        apply mul_le_mul_of_nonneg_right _ hr
        dsimp only [C_U]
        exact le_add_of_nonneg_right hC_d
  · calc
      |deriv (fun s ↦ blockEscortMean B n s u) alpha| +
          |deriv (fun s ↦ blockEscortSecond B n s u) alpha|
          ≤ U * S + U ^ 2 * S := by
        exact add_le_add hmean hsecond
      _ = (U + U ^ 2) * S := by ring
      _ ≤ (U + U ^ 2) * (C * L * r) := by
        apply mul_le_mul_of_nonneg_left _ hUd
        simpa only [S, L, r] using hesc.2
      _ = C_d * L * r := by
        dsimp only [C_d]
        ring
      _ ≤ C_U * L * r := by
        have hCdCU : C_d ≤ C_U := by
          dsimp only [C_U]
          exact le_add_of_nonneg_left hC_m
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCdCU hL) hr
      _ = C_U * Real.log (blockScale n) *
          Real.rpow (blockScale n) (-eta) := rfl

section ShannonBlockIdentities

/-- The mass of the block base is its order-one partition function. -/
theorem blockLineMass_zero_eq_partition_one {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) :
    lineMass (blockLineData B n u) 0 = blockPartition B n 1 := by
  unfold lineMass blockPartition
  simp only [lineRaw, blockLineData, mul_zero, add_zero, mul_one]
  simpa only [Real.rpow_one] using
    (sum_rpow_blockBase_eq_contributions B n 1)

/-- Closed normalized coordinate formula at the block base. -/
theorem lineProb_blockLine_zero_apply {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (i : BlockCarrier B n) :
    letI := blockCarrierNonempty B n
    (lineProb (blockLineData B n u) 0).1 i =
      blockBase B n i / blockPartition B n 1 := by
  letI := blockCarrierNonempty B n
  rw [lineProb_apply_of_positive _ (linePositiveZero _) i,
    blockLineMass_zero_eq_partition_one]
  simp [lineRaw, blockLineData, blockBase, blockVelocity]

/-- Logarithm of one normalized block coordinate. -/
theorem log_lineProb_blockLine_zero_apply {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (i : BlockCarrier B n) :
    letI := blockCarrierNonempty B n
    Real.log ((lineProb (blockLineData B n u) 0).1 i) =
      B.a i.1 * Real.log (blockScale n) - Real.log (blockPartition B n 1) := by
  letI := blockCarrierNonempty B n
  rw [lineProb_blockLine_zero_apply]
  have hbase : 0 < blockBase B n i :=
    Real.rpow_pos_of_pos (blockScale_pos n) (B.a i.1)
  have hpart := blockPartition_pos B n 1
  rw [Real.log_div hbase.ne' hpart.ne']
  change Real.log (Real.rpow (blockScale n) (B.a i.1)) -
      Real.log (blockPartition B n 1) = _
  rw [Real.rpow_eq_pow, Real.log_rpow (blockScale_pos n)]

@[simp] theorem effectiveVelocity_blockLine_zero {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (i : BlockCarrier B n) :
    effectiveVelocity (blockLineData B n u) 0 i = u i.1 := by
  simp [effectiveVelocity, blockLineData, blockVelocity]

/-- Every block escort-centered statistic has weighted sum zero. -/
theorem sum_blockEscort_mul_centered_eq_zero {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) (v : Fin (J + 1) → ℝ) :
    ∑ j, blockEscort B n j alpha *
      (v j - blockEscortMean B n alpha v) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_blockEscort]
  unfold blockEscortMean
  ring

/-- The two equivalent centered forms of a finite weighted covariance. -/
theorem sum_blockEscort_centered_mul_eq_mul_centered {J : ℕ}
    (B : BlockData J) (n : ℕ) (alpha : ℝ)
    (u v : Fin (J + 1) → ℝ) :
    ∑ j, blockEscort B n j alpha *
        (u j - blockEscortMean B n alpha u) * v j =
      ∑ j, blockEscort B n j alpha * u j *
        (v j - blockEscortMean B n alpha v) := by
  let m_u := blockEscortMean B n alpha u
  let m_v := blockEscortMean B n alpha v
  calc
    ∑ j, blockEscort B n j alpha * (u j - m_u) * v j =
        (∑ j, blockEscort B n j alpha * u j * v j) - m_u * m_v := by
      simp_rw [show ∀ j : Fin (J + 1),
        blockEscort B n j alpha * (u j - m_u) * v j =
          blockEscort B n j alpha * u j * v j -
            m_u * (blockEscort B n j alpha * v j) by
        intro j
        ring]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rfl
    _ = ∑ j, blockEscort B n j alpha * u j * (v j - m_v) := by
      symm
      simp_rw [show ∀ j : Fin (J + 1),
        blockEscort B n j alpha * u j * (v j - m_v) =
          blockEscort B n j alpha * u j * v j -
            (blockEscort B n j alpha * u j) * m_v by
        intro j
        ring]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      rfl

/-- The Shannon slope of a block line is an exact centered block covariance. -/
theorem shannonLineSlope_blockLine_zero {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) :
    letI := blockCarrierNonempty B n
    shannonLineSlope (blockLineData B n u) 0 =
      -∑ j, blockEscort B n j 1 *
        (u j - blockEscortMean B n 1 u) *
          (B.a j * Real.log (blockScale n) -
            Real.log (blockPartition B n 1)) := by
  letI := blockCarrierNonempty B n
  let v : Fin (J + 1) → ℝ := fun j ↦
    (u j - blockEscortMean B n 1 u) *
      (B.a j * Real.log (blockScale n) -
        Real.log (blockPartition B n 1))
  have hgroup := sum_escortWeight_mul_blockValue B n u v 1
  unfold shannonLineSlope
  calc
    -∑ i, (lineProb (blockLineData B n u) 0).1 i *
        (effectiveVelocity (blockLineData B n u) 0 i -
          escortMean (blockLineData B n u) 1 0) *
        Real.log ((lineProb (blockLineData B n u) 0).1 i) =
      -∑ i, escortWeight (blockLineData B n u) 1 0 i * v i.1 := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [escortWeight_one_eq_lineProb _ (linePositiveZero _) i,
          log_lineProb_blockLine_zero_apply,
          effectiveVelocity_blockLine_zero, escortMean_blockLine_zero]
        dsimp only [v]
        ring
    _ = -∑ j, blockEscort B n j 1 * v j :=
      congrArg Neg.neg hgroup
    _ = -∑ j, blockEscort B n j 1 *
        (u j - blockEscortMean B n 1 u) *
          (B.a j * Real.log (blockScale n) -
            Real.log (blockPartition B n 1)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [v]
      ring

/-- At the Shannon order, the entropy slope is the negative order
derivative of the block escort velocity mean. -/
theorem shannonLineSlope_blockLine_zero_eq_neg_orderDeriv {J : ℕ}
    (B : BlockData J) (n : ℕ) (u : Fin (J + 1) → ℝ) :
    letI := blockCarrierNonempty B n
    shannonLineSlope (blockLineData B n u) 0 =
      -deriv (fun alpha ↦ blockEscortMean B n alpha u) 1 := by
  letI := blockCarrierNonempty B n
  let p : Fin (J + 1) → ℝ := fun j ↦ blockEscort B n j 1
  let m_u := blockEscortMean B n 1 u
  let m_a := blockEscortMean B n 1 B.a
  let L := Real.log (blockScale n)
  let z := Real.log (blockPartition B n 1)
  have hu0 : ∑ j, p j * (u j - m_u) = 0 := by
    simpa only [p, m_u] using sum_blockEscort_mul_centered_eq_zero B n 1 u
  have hcov : ∑ j, p j * (u j - m_u) * B.a j =
      ∑ j, p j * u j * (B.a j - m_a) := by
    simpa only [p, m_u, m_a] using
      sum_blockEscort_centered_mul_eq_mul_centered B n 1 u B.a
  have haffine :
      ∑ j, p j * (u j - m_u) * (B.a j * L - z) =
        L * (∑ j, p j * (u j - m_u) * B.a j) := by
    calc
      ∑ j, p j * (u j - m_u) * (B.a j * L - z) =
          L * (∑ j, p j * (u j - m_u) * B.a j) -
            z * (∑ j, p j * (u j - m_u)) := by
        simp_rw [show ∀ j : Fin (J + 1),
          p j * (u j - m_u) * (B.a j * L - z) =
            L * (p j * (u j - m_u) * B.a j) -
              z * (p j * (u j - m_u)) by
          intro j
          ring]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = L * (∑ j, p j * (u j - m_u) * B.a j) := by
        rw [hu0]
        ring
  rw [shannonLineSlope_blockLine_zero, deriv_blockEscortMean_order]
  simp_rw [deriv_blockEscort]
  change -(∑ j, p j * (u j - m_u) * (B.a j * L - z)) =
    -(∑ j, L * p j * (B.a j - m_a) * u j)
  rw [haffine, hcov]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Shannon specialization of the first block kernel. -/
theorem blockKernelFirst_one {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) :
    blockKernelFirst B n u 1 =
      -deriv (fun alpha ↦ blockEscortMean B n alpha u) 1 := by
  letI := blockCarrierNonempty B n
  rw [blockKernelFirst, entropyLineFirst_one _ (linePositiveZero _),
    shannonLineSlope_blockLine_zero_eq_neg_orderDeriv]

/-- Shannon specialization of the second block kernel. -/
theorem blockKernelSecond_one {J : ℕ} (B : BlockData J) (n : ℕ)
    (u : Fin (J + 1) → ℝ) :
    blockKernelSecond B n u 1 =
      -blockEscortVar B n 1 u -
        2 * blockEscortMean B n 1 u * blockKernelFirst B n u 1 := by
  letI := blockCarrierNonempty B n
  rw [blockKernelSecond, entropyLineSecond_one _ (linePositiveZero _),
    escortVar_blockLine_zero, escortMean_blockLine_zero,
    blockKernelFirst, entropyLineFirst_one _ (linePositiveZero _)]

end ShannonBlockIdentities

section NearShannon

/-- An escort average of a uniformly bounded statistic is bounded by the
same constant. -/
theorem abs_blockEscortMean_le {J : ℕ} (B : BlockData J) (n : ℕ)
    (alpha : ℝ) (u : Fin (J + 1) → ℝ) (U : ℝ)
    (h_u : ∀ j, |u j| ≤ U) :
    |blockEscortMean B n alpha u| ≤ U := by
  unfold blockEscortMean
  calc
    |∑ j, blockEscort B n j alpha * u j|
        ≤ ∑ j, |blockEscort B n j alpha * u j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, blockEscort B n j alpha * U := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (blockEscort_nonneg B n j alpha)]
      exact mul_le_mul_of_nonneg_left (h_u j) (blockEscort_nonneg B n j alpha)
    _ = U := by
      rw [← Finset.sum_mul, sum_blockEscort, one_mul]

/-- Mean-value estimate for an escort mean on a closed interval. -/
theorem abs_blockEscortMean_sub_le_of_deriv_bound {J : ℕ}
    (B : BlockData J) (n : ℕ) (u : Fin (J + 1) → ℝ)
    {lo hi alpha K : ℝ} (h_alpha : alpha ∈ Icc lo hi)
    (h_one : (1 : ℝ) ∈ Icc lo hi)
    (hK : ∀ s ∈ Icc lo hi,
      |deriv (fun t ↦ blockEscortMean B n t u) s| ≤ K) :
    |blockEscortMean B n alpha u - blockEscortMean B n 1 u| ≤
      K * |alpha - 1| := by
  have hmvt := (convex_Icc lo hi).norm_image_sub_le_of_norm_deriv_le
    (f := fun t ↦ blockEscortMean B n t u)
    (C := K)
    (fun s _ ↦ (hasDerivAt_blockEscortMean_order B n u s).differentiableAt)
    (fun s hs ↦ by simpa only [Real.norm_eq_abs] using hK s hs)
    h_one h_alpha
  simpa only [Real.norm_eq_abs] using hmvt

/-- The singular coefficient cancels the distance to Shannon order. -/
theorem abs_singularWeight_mul_sub_le {alpha x y K : ℝ}
    (h_alpha : 0 < alpha) (h_one : alpha ≠ 1) (h_two : alpha ≤ 2)
    (hK : 0 ≤ K) (hxy : |x - y| ≤ K * |alpha - 1|) :
    |singularWeight (finiteParam alpha) * (x - y)| ≤ 2 * K := by
  rw [singularWeight_finite h_alpha.le h_one, abs_mul]
  calc
    |alpha / (1 - alpha)| * |x - y|
        ≤ |alpha / (1 - alpha)| * (K * |alpha - 1|) :=
      mul_le_mul_of_nonneg_left hxy (abs_nonneg _)
    _ = alpha * K := by
      rw [abs_div, abs_of_pos h_alpha, abs_sub_comm (1 : ℝ) alpha]
      have hne : |alpha - 1| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr h_one)
      field_simp [hne]
    _ ≤ 2 * K := mul_le_mul_of_nonneg_right h_two hK

/-- Difference of squared escort means under a uniform velocity bound. -/
theorem abs_sq_blockEscortMean_sub_sq_le {J : ℕ} (B : BlockData J)
    (n : ℕ) (alpha : ℝ) (u : Fin (J + 1) → ℝ) (U : ℝ)
    (h_u : ∀ j, |u j| ≤ U) :
    |(blockEscortMean B n 1 u) ^ 2 -
        (blockEscortMean B n alpha u) ^ 2| ≤
      (2 * U) *
        |blockEscortMean B n alpha u - blockEscortMean B n 1 u| := by
  have h1 := abs_blockEscortMean_le B n 1 u U h_u
  have ha := abs_blockEscortMean_le B n alpha u U h_u
  have hsum : |blockEscortMean B n 1 u + blockEscortMean B n alpha u| ≤
      2 * U := by
    calc
      |blockEscortMean B n 1 u + blockEscortMean B n alpha u|
          ≤ |blockEscortMean B n 1 u| +
            |blockEscortMean B n alpha u| := abs_add_le _ _
      _ ≤ U + U := add_le_add h1 ha
      _ = 2 * U := by ring
  rw [show (blockEscortMean B n 1 u) ^ 2 -
      (blockEscortMean B n alpha u) ^ 2 =
      (blockEscortMean B n 1 u - blockEscortMean B n alpha u) *
        (blockEscortMean B n 1 u + blockEscortMean B n alpha u) by ring,
    abs_mul, abs_sub_comm]
  have hmul := mul_le_mul_of_nonneg_left hsum
    (abs_nonneg (blockEscortMean B n alpha u - blockEscortMean B n 1 u))
  simpa only [mul_comm] using hmul

/-- Uniform near-Shannon kernel bound under a fixed dominant exponent gap. -/
theorem nearShannonDominantBound {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1)) (delta eta U : ℝ)
    (h_delta : 0 < delta) (h_delta_one : delta < 1)
    (h_eta : 0 < eta) (h_U : 0 ≤ U)
    (hgap : ∀ alpha ∈ Icc (1 - delta) (1 + delta),
      ∀ j : Fin (J + 1), j ≠ k →
        eta ≤ blockExponent B k alpha - blockExponent B j alpha) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (u : Fin (J + 1) → ℝ),
        (∀ j, |u j| ≤ U) →
        ∀ alpha ∈ Icc (1 - delta) (1 + delta),
          |blockKernelFirst B n u (finiteParam alpha)| +
              |blockKernelSecond B n u (finiteParam alpha)| ≤
            C * (1 + Real.log (blockScale n)) *
              Real.rpow (blockScale n) (-eta) := by
  have hdom := dominantBlock B (Icc (1 - delta) (1 + delta)) k eta h_eta hgap
  obtain ⟨C₀, hC₀, hC₀bound⟩ := hdom.2 U h_U
  let C : ℝ := (4 + 4 * U) * C₀
  have hfactor : 0 ≤ 4 + 4 * U := by positivity
  have hC : 0 ≤ C := mul_nonneg hfactor hC₀
  refine ⟨C, hC, ?_⟩
  intro n u hu alpha h_alpha
  let L := Real.log (blockScale n)
  let r := Real.rpow (blockScale n) (-eta)
  let q := C₀ * r
  let K := C₀ * L * r
  have hL : 0 ≤ L := log_blockScale_nonneg n
  have hr : 0 ≤ r := Real.rpow_nonneg (blockScale_pos n).le _
  have hq : 0 ≤ q := mul_nonneg hC₀ hr
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hC₀ hL) hr
  have h_one_mem : (1 : ℝ) ∈ Icc (1 - delta) (1 + delta) := by
    constructor <;> linarith
  have hpack := hC₀bound u hu n alpha h_alpha
  have hpack_one := hC₀bound u hu n 1 h_one_mem
  have hvar : blockEscortVar B n alpha u ≤ q := by
    dsimp only [q, r]
    linarith [abs_nonneg (blockEscortMean B n alpha u - u k),
      abs_nonneg (blockEscortSecond B n alpha u - (u k) ^ 2)]
  have hvar_one : blockEscortVar B n 1 u ≤ q := by
    dsimp only [q, r]
    linarith [abs_nonneg (blockEscortMean B n 1 u - u k),
      abs_nonneg (blockEscortSecond B n 1 u - (u k) ^ 2)]
  have hderivMean : ∀ s ∈ Icc (1 - delta) (1 + delta),
      |deriv (fun t ↦ blockEscortMean B n t u) s| ≤ K := by
    intro s hs
    have hp := hC₀bound u hu n s hs
    dsimp only [K, L, r]
    linarith [abs_nonneg (deriv (fun t ↦ blockEscortSecond B n t u) s)]
  have hmeanDiff :
      |blockEscortMean B n alpha u - blockEscortMean B n 1 u| ≤
        K * |alpha - 1| :=
    abs_blockEscortMean_sub_le_of_deriv_bound B n u h_alpha h_one_mem hderivMean
  have h_alpha_pos : 0 < alpha := by
    linarith [h_alpha.1]
  have h_alpha_two : alpha ≤ 2 := by
    linarith [h_alpha.2]
  by_cases h_alpha_one : alpha = 1
  · subst alpha
    rw [finiteParam_one, blockKernelFirst_one, blockKernelSecond_one,
      abs_neg]
    have hfirst :
        |deriv (fun t ↦ blockEscortMean B n t u) 1| ≤ K :=
      hderivMean 1 h_one_mem
    have hmeanOne := abs_blockEscortMean_le B n 1 u U hu
    have hsecond :
        |-blockEscortVar B n 1 u -
          2 * blockEscortMean B n 1 u *
            blockKernelFirst B n u 1| ≤ q + 2 * U * K := by
      calc
        |-blockEscortVar B n 1 u -
            2 * blockEscortMean B n 1 u * blockKernelFirst B n u 1|
            ≤ |-blockEscortVar B n 1 u| +
              |2 * blockEscortMean B n 1 u * blockKernelFirst B n u 1| :=
          abs_sub _ _
        _ ≤ q + 2 * U * K := by
          rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          have hfirstKernel : |blockKernelFirst B n u 1| ≤ K := by
            rw [blockKernelFirst_one, abs_neg]
            exact hfirst
          have habsVar : |blockEscortVar B n 1 u| ≤ q := by
            rw [abs_of_nonneg (blockEscortVar_nonneg B n 1 u)]
            exact hvar_one
          exact add_le_add habsVar
            (mul_le_mul (mul_le_mul_of_nonneg_left hmeanOne (by norm_num))
              hfirstKernel (abs_nonneg _) (mul_nonneg (by norm_num) h_U))
    have hraw :
        |deriv (fun t ↦ blockEscortMean B n t u) 1| +
          |-blockEscortVar B n 1 u -
            2 * blockEscortMean B n 1 u * blockKernelFirst B n u 1| ≤
          q + (1 + 2 * U) * K := by
      calc
        _ ≤ K + (q + 2 * U * K) := add_le_add hfirst hsecond
        _ = q + (1 + 2 * U) * K := by ring
    calc
      _ ≤ q + (1 + 2 * U) * K := hraw
      _ ≤ C * (1 + L) * r := by
        have hdiff : 0 ≤ (3 + 4 * U) + (3 + 2 * U) * L := by
          exact add_nonneg (by positivity) (mul_nonneg (by positivity) hL)
        have hcoef : 1 + (1 + 2 * U) * L ≤
            (4 + 4 * U) * (1 + L) := by linarith
        calc
          q + (1 + 2 * U) * K = (1 + (1 + 2 * U) * L) * q := by
            dsimp only [q, K]
            ring
          _ ≤ ((4 + 4 * U) * (1 + L)) * q :=
            mul_le_mul_of_nonneg_right hcoef hq
          _ = C * (1 + L) * r := by
            dsimp only [q, C]
            ring
      _ = C * (1 + Real.log (blockScale n)) *
          Real.rpow (blockScale n) (-eta) := rfl
  · have hfirst : |blockKernelFirst B n u (finiteParam alpha)| ≤
        2 * K := by
      rw [blockKernelFirst_finite B n u h_alpha_pos h_alpha_one]
      exact abs_singularWeight_mul_sub_le h_alpha_pos h_alpha_one h_alpha_two
        hK hmeanDiff
    have hsq :
        |(blockEscortMean B n 1 u) ^ 2 -
            (blockEscortMean B n alpha u) ^ 2| ≤
          ((2 * U) * K) * |alpha - 1| := by
      calc
        _ ≤ (2 * U) *
            |blockEscortMean B n alpha u - blockEscortMean B n 1 u| :=
          abs_sq_blockEscortMean_sub_sq_le B n alpha u U hu
        _ ≤ (2 * U) * (K * |alpha - 1|) :=
          mul_le_mul_of_nonneg_left hmeanDiff (mul_nonneg (by norm_num) h_U)
        _ = ((2 * U) * K) * |alpha - 1| := by ring
    have hsingSq :
        |singularWeight (finiteParam alpha) *
          ((blockEscortMean B n 1 u) ^ 2 -
            (blockEscortMean B n alpha u) ^ 2)| ≤
          2 * ((2 * U) * K) := by
      exact abs_singularWeight_mul_sub_le h_alpha_pos h_alpha_one h_alpha_two
        (mul_nonneg (mul_nonneg (by norm_num) h_U) hK) hsq
    have hsecond : |blockKernelSecond B n u (finiteParam alpha)| ≤
        2 * q + 4 * U * K := by
      rw [blockKernelSecond_finite B n u h_alpha_pos h_alpha_one]
      calc
        |(-alpha * blockEscortVar B n alpha u +
            singularWeight (finiteParam alpha) *
              ((blockEscortMean B n 1 u) ^ 2 -
                (blockEscortMean B n alpha u) ^ 2))|
            ≤ |-alpha * blockEscortVar B n alpha u| +
              |singularWeight (finiteParam alpha) *
                ((blockEscortMean B n 1 u) ^ 2 -
                  (blockEscortMean B n alpha u) ^ 2)| := abs_add_le _ _
        _ ≤ 2 * q + 4 * U * K := by
          rw [abs_mul, abs_neg, abs_of_pos h_alpha_pos,
            abs_of_nonneg (blockEscortVar_nonneg B n alpha u)]
          have hvarTerm : alpha * blockEscortVar B n alpha u ≤ 2 * q :=
            mul_le_mul h_alpha_two hvar (blockEscortVar_nonneg B n alpha u) (by norm_num)
          calc
            alpha * blockEscortVar B n alpha u +
                |singularWeight (finiteParam alpha) *
                  ((blockEscortMean B n 1 u) ^ 2 -
                    (blockEscortMean B n alpha u) ^ 2)|
                ≤ 2 * q + 2 * ((2 * U) * K) :=
              add_le_add hvarTerm hsingSq
            _ = 2 * q + 4 * U * K := by ring
    calc
      _ ≤ 2 * K + (2 * q + 4 * U * K) := add_le_add hfirst hsecond
      _ = 2 * q + (2 + 4 * U) * K := by ring
      _ ≤ C * (1 + L) * r := by
        have hdiff : 0 ≤ (2 + 4 * U) + 2 * L := by positivity
        have hcoef : 2 + (2 + 4 * U) * L ≤
            (4 + 4 * U) * (1 + L) := by linarith
        calc
          2 * q + (2 + 4 * U) * K = (2 + (2 + 4 * U) * L) * q := by
            dsimp only [q, K]
            ring
          _ ≤ ((4 + 4 * U) * (1 + L)) * q :=
            mul_le_mul_of_nonneg_right hcoef hq
          _ = C * (1 + L) * r := by
            dsimp only [q, C]
            ring
      _ = C * (1 + Real.log (blockScale n)) *
          Real.rpow (blockScale n) (-eta) := rfl

/-- The shifted natural block scale tends to infinity. -/
theorem tendsto_blockScale_atTop : Tendsto blockScale atTop atTop := by
  change Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop
  exact tendsto_atTop_add_const_right atTop (2 : ℝ)
    (tendsto_natCast_atTop_atTop (R := ℝ))

/-- A logarithmic factor is dominated by every positive inverse power along
the block scale. -/
theorem tendsto_one_add_log_mul_rpow_blockScale (eta : ℝ) (h_eta : 0 < eta) :
    Tendsto (fun n : ℕ ↦
      (1 + Real.log (blockScale n)) *
        Real.rpow (blockScale n) (-eta)) atTop (nhds 0) := by
  have hrReal := tendsto_rpow_neg_atTop h_eta
  have hr : Tendsto (fun n : ℕ ↦ (blockScale n) ^ (-eta)) atTop (nhds 0) :=
    hrReal.comp tendsto_blockScale_atTop
  have hlogDiv : Tendsto (fun x : ℝ ↦ Real.log x / x ^ eta)
      atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop h_eta).tendsto_div_nhds_zero
  have hlogMulReal : Tendsto (fun x : ℝ ↦
      Real.log x * x ^ (-eta)) atTop (nhds 0) := by
    apply hlogDiv.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_neg hx.le, div_eq_mul_inv]
  have hlogMul : Tendsto (fun n : ℕ ↦
      Real.log (blockScale n) * (blockScale n) ^ (-eta)) atTop (nhds 0) :=
    hlogMulReal.comp tendsto_blockScale_atTop
  have hsum := hr.add hlogMul
  simpa only [Real.rpow_eq_pow, add_zero, add_mul, one_mul] using hsum

/-- Literal near-Shannon dominant-block package, including decay of the
uniform majorant. -/
theorem nearShannonDominant {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1)) (delta eta U : ℝ)
    (h_delta : 0 < delta) (h_delta_one : delta < 1)
    (h_eta : 0 < eta) (h_U : 0 ≤ U)
    (hgap : ∀ alpha ∈ Icc (1 - delta) (1 + delta),
      ∀ j : Fin (J + 1), j ≠ k →
        eta ≤ blockExponent B k alpha - blockExponent B j alpha) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (n : ℕ) (u : Fin (J + 1) → ℝ),
        (∀ j, |u j| ≤ U) →
        ∀ alpha ∈ Icc (1 - delta) (1 + delta),
          |blockKernelFirst B n u (finiteParam alpha)| +
              |blockKernelSecond B n u (finiteParam alpha)| ≤
            C * (1 + Real.log (blockScale n)) *
              Real.rpow (blockScale n) (-eta)) ∧
      Tendsto (fun n : ℕ ↦
        C * (1 + Real.log (blockScale n)) *
          Real.rpow (blockScale n) (-eta)) atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ := nearShannonDominantBound B k delta eta U
    h_delta h_delta_one h_eta h_U hgap
  refine ⟨C, hC, hbound, ?_⟩
  have hlim := tendsto_one_add_log_mul_rpow_blockScale eta h_eta
  simpa only [mul_zero, mul_assoc] using tendsto_const_nhds.mul hlim

end NearShannon

section LargeAlpha

/-- A total positive slope gap: the distinguished coordinate is assigned the
harmless value one, while every other coordinate records its strict amplitude
gap from the distinguished block. -/
def largeAlphaSlopeGap {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1)) : ℝ :=
  finMin (fun j : Fin (J + 1) ↦ if j = k then 1 else B.a k - B.a j)

/-- A finite bound for all intercept differences from the distinguished
block. -/
def largeAlphaInterceptBound {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1)) : ℝ :=
  finMax (fun j : Fin (J + 1) ↦ |B.m k - B.m j|)

theorem largeAlphaSlopeGap_pos {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1))
    (hstrict : ∀ j : Fin (J + 1), j ≠ k → B.a j < B.a k) :
    0 < largeAlphaSlopeGap B k := by
  obtain ⟨j, hj⟩ := finMin_mem
    (fun j : Fin (J + 1) ↦ if j = k then 1 else B.a k - B.a j)
  change 0 < finMin
    (fun j : Fin (J + 1) ↦ if j = k then 1 else B.a k - B.a j)
  rw [← hj]
  by_cases hjk : j = k
  · simp [hjk]
  · simp only [hjk, ↓reduceIte]
    exact sub_pos.mpr (hstrict j hjk)

theorem largeAlphaSlopeGap_le {J : ℕ} (B : BlockData J)
    (k j : Fin (J + 1)) (hjk : j ≠ k) :
    largeAlphaSlopeGap B k ≤ B.a k - B.a j := by
  have hle := finMin_le
    (fun l : Fin (J + 1) ↦ if l = k then 1 else B.a k - B.a l) j
  simpa only [largeAlphaSlopeGap, hjk, ↓reduceIte] using hle

theorem largeAlphaInterceptBound_nonneg {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1)) :
    0 ≤ largeAlphaInterceptBound B k := by
  have hk := le_finMax_family
    (fun j : Fin (J + 1) ↦ |B.m k - B.m j|) k
  simpa only [largeAlphaInterceptBound, sub_self, abs_zero] using hk

theorem abs_intercept_sub_le_largeAlphaInterceptBound {J : ℕ}
    (B : BlockData J) (k j : Fin (J + 1)) :
    |B.m k - B.m j| ≤ largeAlphaInterceptBound B k := by
  exact le_finMax_family (fun l : Fin (J + 1) ↦ |B.m k - B.m l|) j

/-- Beyond an explicit threshold, half the strict amplitude gap survives the
fixed intercept differences as a linearly growing exponent gap. -/
theorem largeAlpha_exponent_gap {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1))
    (hstrict : ∀ j : Fin (J + 1), j ≠ k → B.a j < B.a k)
    {alpha : ℝ}
    (h_alpha : max 2
      (largeAlphaInterceptBound B k / (largeAlphaSlopeGap B k / 2)) ≤ alpha) :
    ∀ j : Fin (J + 1), j ≠ k →
      (largeAlphaSlopeGap B k / 2) * alpha ≤
        blockExponent B k alpha - blockExponent B j alpha := by
  intro j hjk
  let delta := largeAlphaSlopeGap B k
  let gamma := delta / 2
  let M := largeAlphaInterceptBound B k
  have hdelta : 0 < delta := largeAlphaSlopeGap_pos B k hstrict
  have hgamma : 0 < gamma := by dsimp only [gamma]; linarith
  have hM : 0 ≤ M := by
    simpa only [M] using largeAlphaInterceptBound_nonneg B k
  have h_alpha_two : 2 ≤ alpha := (le_max_left _ _).trans h_alpha
  have h_alpha_ratio : M / gamma ≤ alpha :=
    (le_max_right _ _).trans h_alpha
  have hMalpha : M ≤ alpha * gamma :=
    (div_le_iff₀ hgamma).mp h_alpha_ratio
  have hintercept : -M ≤ B.m k - B.m j := by
    have habs := abs_intercept_sub_le_largeAlphaInterceptBound B k j
    rw [abs_le] at habs
    simpa only [M] using habs.1
  have hslope : delta ≤ B.a k - B.a j := by
    simpa only [delta] using largeAlphaSlopeGap_le B k j hjk
  have halpha_nonneg : 0 ≤ alpha := by linarith
  have hslopeAlpha : delta * alpha ≤ (B.a k - B.a j) * alpha :=
    mul_le_mul_of_nonneg_right hslope halpha_nonneg
  have hmain : gamma * alpha ≤
      (B.m k - B.m j) + (B.a k - B.a j) * alpha := by
    have hdeltaGamma : delta = 2 * gamma := by
      dsimp only [gamma]
      ring
    nlinarith
  calc
    gamma * alpha
        ≤ (B.m k - B.m j) + (B.a k - B.a j) * alpha := hmain
    _ = blockExponent B k alpha - blockExponent B j alpha := by
      unfold blockExponent
      ring

/-- Uniform elementary bound for the linearly weighted exponential tail.
The shifted block scale is at least two, so the constant depends only on the
positive decay rate. -/
theorem alpha_mul_rpow_blockScale_le_inv {gamma alpha : ℝ} (n : ℕ)
    (h_gamma : 0 < gamma) (h_alpha : 0 ≤ alpha) :
    alpha * Real.rpow (blockScale n) (-gamma * alpha) ≤
      (gamma * Real.log 2)⁻¹ := by
  let c := gamma * Real.log 2
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc : 0 < c := mul_pos h_gamma hlog2
  have hlog : Real.log (2 : ℝ) ≤ Real.log (blockScale n) := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) (blockScale_pos n)
      (by
        unfold blockScale
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith)
  have hexp :
      Real.rpow (blockScale n) (-gamma * alpha) ≤
        Real.exp (-(c * alpha)) := by
    change (blockScale n) ^ (-gamma * alpha) ≤ Real.exp (-(c * alpha))
    rw [Real.rpow_def_of_pos (blockScale_pos n)]
    apply Real.exp_le_exp.mpr
    have hneg : -gamma * alpha ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h_gamma.le) h_alpha
    calc
      Real.log (blockScale n) * (-gamma * alpha)
          ≤ Real.log 2 * (-gamma * alpha) :=
        mul_le_mul_of_nonpos_right hlog hneg
      _ = -(c * alpha) := by dsimp only [c]; ring
  calc
    alpha * Real.rpow (blockScale n) (-gamma * alpha)
        ≤ alpha * Real.exp (-(c * alpha)) :=
      mul_le_mul_of_nonneg_left hexp h_alpha
    _ = c⁻¹ * ((c * alpha) * Real.exp (-(c * alpha))) := by
      field_simp [hc.ne']
    _ ≤ c⁻¹ * Real.exp (-1) :=
      mul_le_mul_of_nonneg_left (Real.mul_exp_neg_le_exp_neg_one (c * alpha))
        (inv_nonneg.mpr hc.le)
    _ ≤ c⁻¹ * 1 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      exact (Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0))
    _ = (gamma * Real.log 2)⁻¹ := by simp only [c, mul_one]

/-- Explicit outside-escort decay supplied by the linearly growing exponent
gap. -/
theorem largeAlpha_outside_le {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1))
    (hstrict : ∀ j : Fin (J + 1), j ≠ k → B.a j < B.a k)
    {alpha : ℝ}
    (h_alpha : max 2
      (largeAlphaInterceptBound B k / (largeAlphaSlopeGap B k / 2)) ≤ alpha)
    (n : ℕ) :
    ∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha ≤
      (2 * Fintype.card (Fin (J + 1))) *
        Real.rpow (blockScale n)
          (-(largeAlphaSlopeGap B k / 2) * alpha) := by
  let gamma := largeAlphaSlopeGap B k / 2
  have hgap := largeAlpha_exponent_gap B k hstrict h_alpha
  have hdecay : 0 ≤ 2 * Real.rpow (blockScale n) (-gamma * alpha) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (blockScale_pos n).le _)
  calc
    ∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha
        ≤ ∑ _j ∈ Finset.univ.erase k,
            2 * Real.rpow (blockScale n) (-gamma * alpha) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [neg_mul] using
        (blockEscort_le_two_mul_decay B n k j alpha (gamma * alpha)
          (hgap j (Finset.ne_of_mem_erase hj)))
    _ = ((Finset.univ.erase k).card : ℝ) *
          (2 * Real.rpow (blockScale n) (-gamma * alpha)) := by simp
    _ ≤ (Fintype.card (Fin (J + 1)) : ℝ) *
          (2 * Real.rpow (blockScale n) (-gamma * alpha)) := by
      apply mul_le_mul_of_nonneg_right _ hdecay
      exact_mod_cast Finset.card_le_card (Finset.erase_subset k Finset.univ)
    _ = (2 * Fintype.card (Fin (J + 1))) *
          Real.rpow (blockScale n)
            (-(largeAlphaSlopeGap B k / 2) * alpha) := by
      dsimp only [gamma]
      ring

/-- The same tail remains uniformly bounded after multiplication by the
order parameter. -/
theorem largeAlpha_mul_outside_le {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1))
    (hstrict : ∀ j : Fin (J + 1), j ≠ k → B.a j < B.a k)
    {alpha : ℝ}
    (h_alpha : max 2
      (largeAlphaInterceptBound B k / (largeAlphaSlopeGap B k / 2)) ≤ alpha)
    (n : ℕ) :
    alpha * (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha) ≤
      (2 * Fintype.card (Fin (J + 1))) *
        ((largeAlphaSlopeGap B k / 2) * Real.log 2)⁻¹ := by
  let gamma := largeAlphaSlopeGap B k / 2
  have hdelta := largeAlphaSlopeGap_pos B k hstrict
  have hgamma : 0 < gamma := by dsimp only [gamma]; linarith
  have halpha : 0 ≤ alpha := by
    have htwo : (2 : ℝ) ≤ alpha := (le_max_left _ _).trans h_alpha
    linarith
  have hout := largeAlpha_outside_le B k hstrict h_alpha n
  have hN : 0 ≤ (2 * Fintype.card (Fin (J + 1)) : ℝ) := by positivity
  have hmul :
      alpha * (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha) ≤
        alpha * ((2 * Fintype.card (Fin (J + 1))) *
          Real.rpow (blockScale n) (-gamma * alpha)) :=
    mul_le_mul_of_nonneg_left (by simpa only [gamma] using hout) halpha
  calc
    alpha * (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha)
        ≤ (2 * Fintype.card (Fin (J + 1))) *
            (alpha * Real.rpow (blockScale n) (-gamma * alpha)) := by
      calc
        _ ≤ alpha * ((2 * Fintype.card (Fin (J + 1))) *
            Real.rpow (blockScale n) (-gamma * alpha)) := hmul
        _ = _ := by ring
    _ ≤ (2 * Fintype.card (Fin (J + 1))) *
          (gamma * Real.log 2)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (alpha_mul_rpow_blockScale_le_inv n hgamma halpha) hN
    _ = (2 * Fintype.card (Fin (J + 1))) *
        ((largeAlphaSlopeGap B k / 2) * Real.log 2)⁻¹ := rfl

/-- Strict amplitude maximality persists on a symmetric neighborhood of the
block-line base point.  Ties inside the maximal block have identical line
velocity, exactly as required by `FixedMaxCoordinate`. -/
theorem exists_fixedMaxCoordinate_blockLine {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1))
    (hstrict : ∀ j : Fin (J + 1), j ≠ k → B.a j < B.a k)
    (n : ℕ) (u : Fin (J + 1) → ℝ) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      FixedMaxCoordinate (blockLineData B n u) (Ioo (-epsilon) epsilon)
        ⟨k, ⟨0, blockCount_pos B n k⟩⟩ := by
  let L := blockLineData B n u
  let istar : BlockCarrier B n := ⟨k, ⟨0, blockCount_pos B n k⟩⟩
  have hposEventually :
      ∀ᶠ lambda in nhds (0 : ℝ), ∀ i : BlockCarrier B n,
        0 < lineRaw L lambda i := by
    rw [Filter.eventually_all]
    intro i
    have hcont : ContinuousAt (fun lambda ↦ lineRaw L lambda i) 0 :=
      (hasDerivAt_lineRaw L 0 i).continuousAt
    exact continuousAt_const.eventually_lt hcont (by
      dsimp only [L]
      exact linePositiveZero (blockLineData B n u) i)
  have hmaxEventually :
      ∀ᶠ lambda in nhds (0 : ℝ), ∀ i : BlockCarrier B n,
        i.1 ≠ k → lineRaw L lambda i < lineRaw L lambda istar := by
    rw [Filter.eventually_all]
    intro i
    by_cases hik : i.1 = k
    · exact Filter.Eventually.of_forall fun _ hi ↦ (hi hik).elim
    · have hconti : ContinuousAt (fun lambda ↦ lineRaw L lambda i) 0 :=
        (hasDerivAt_lineRaw L 0 i).continuousAt
      have hcontstar : ContinuousAt (fun lambda ↦ lineRaw L lambda istar) 0 :=
        (hasDerivAt_lineRaw L 0 istar).continuousAt
      have hbase : lineRaw L 0 i < lineRaw L 0 istar := by
        dsimp only [L, istar]
        simp only [lineRaw, blockLineData, mul_zero, add_zero, mul_one,
          blockBase]
        exact Real.rpow_lt_rpow_of_exponent_lt
          (by
            unfold blockScale
            have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
            linarith)
          (hstrict i.1 hik)
      exact (hconti.eventually_lt hcontstar hbase).mono fun _ hlt _ ↦ hlt
  have hgood := hposEventually.and hmaxEventually
  obtain ⟨lo, hi, hlohi, hsubset⟩ := hgood.exists_Ioo_subset
  let epsilon := min (-lo) hi
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    exact lt_min (neg_pos.mpr hlohi.1) hlohi.2
  refine ⟨epsilon, hepsilon, ?_⟩
  intro lambda hlambda
  have hlambdaGood :
      (∀ i : BlockCarrier B n, 0 < lineRaw L lambda i) ∧
        (∀ i : BlockCarrier B n,
          i.1 ≠ k → lineRaw L lambda i < lineRaw L lambda istar) := by
    apply hsubset
    have hlo : lo < 0 := hlohi.1
    have hhi : 0 < hi := hlohi.2
    have hepsLo : epsilon ≤ -lo := by
      dsimp only [epsilon]
      exact min_le_left _ _
    have hepsHi : epsilon ≤ hi := by
      dsimp only [epsilon]
      exact min_le_right _ _
    constructor
    · exact lt_of_le_of_lt (by linarith : lo ≤ -epsilon) hlambda.1
    · exact lt_of_lt_of_le hlambda.2 hepsHi
  refine ⟨?_, ?_, ?_⟩
  · change ∀ i : BlockCarrier B n,
      0 < lineRaw (blockLineData B n u) lambda i
    simpa only [L] using hlambdaGood.1
  · intro i
    by_cases hik : i.1 = k
    · simp only [lineRaw, blockLineData, blockBase, blockVelocity, hik]
      exact le_rfl
    · exact (hlambdaGood.2 i hik).le
  · intro i heq
    by_cases hik : i.1 = k
    · simp only [effectiveVelocity, blockLineData, blockVelocity, hik]
    · exact (hlambdaGood.2 i hik).ne heq |>.elim

/-- Closed first line kernel at the min-entropy endpoint for a uniquely
maximal amplitude block. -/
theorem blockKernelFirst_top_eq {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1))
    (hstrict : ∀ j : Fin (J + 1), j ≠ k → B.a j < B.a k)
    (n : ℕ) (u : Fin (J + 1) → ℝ) :
    blockKernelFirst B n u ⊤ = blockEscortMean B n 1 u - u k := by
  obtain ⟨epsilon, hepsilon, hfixed⟩ :=
    exists_fixedMaxCoordinate_blockLine B k hstrict n u
  letI := blockCarrierNonempty B n
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := by
    constructor <;> linarith
  rw [blockKernelFirst,
    entropyLineFirst_top_on (blockLineData B n u) isOpen_Ioo hfixed hzero,
    escortMean_blockLine_zero, effectiveVelocity_blockLine_zero]

/-- Closed second line kernel at the min-entropy endpoint for a uniquely
maximal amplitude block. -/
theorem blockKernelSecond_top_eq {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1))
    (hstrict : ∀ j : Fin (J + 1), j ≠ k → B.a j < B.a k)
    (n : ℕ) (u : Fin (J + 1) → ℝ) :
    blockKernelSecond B n u ⊤ =
      (u k) ^ 2 - (blockEscortMean B n 1 u) ^ 2 := by
  obtain ⟨epsilon, hepsilon, hfixed⟩ :=
    exists_fixedMaxCoordinate_blockLine B k hstrict n u
  letI := blockCarrierNonempty B n
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := by
    constructor <;> linarith
  rw [blockKernelSecond,
    entropyLineSecond_top_on (blockLineData B n u) isOpen_Ioo hfixed hzero,
    effectiveVelocity_blockLine_zero, escortMean_blockLine_zero]

theorem abs_blockKernelFirst_top_le {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1))
    (hstrict : ∀ j : Fin (J + 1), j ≠ k → B.a j < B.a k)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (U : ℝ)
    (h_u : ∀ j, |u j| ≤ U) :
    |blockKernelFirst B n u ⊤| ≤ 2 * U := by
  rw [blockKernelFirst_top_eq B k hstrict]
  calc
    |blockEscortMean B n 1 u - u k|
        ≤ |blockEscortMean B n 1 u| + |u k| := abs_sub _ _
    _ ≤ U + U := add_le_add (abs_blockEscortMean_le B n 1 u U h_u) (h_u k)
    _ = 2 * U := by ring

theorem abs_blockKernelSecond_top_le {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1))
    (hstrict : ∀ j : Fin (J + 1), j ≠ k → B.a j < B.a k)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (U : ℝ) (h_U : 0 ≤ U)
    (h_u : ∀ j, |u j| ≤ U) :
    |blockKernelSecond B n u ⊤| ≤ 2 * U ^ 2 := by
  rw [blockKernelSecond_top_eq B k hstrict]
  have hmean := abs_blockEscortMean_le B n 1 u U h_u
  have hmeanSq : (blockEscortMean B n 1 u) ^ 2 ≤ U ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_nonneg h_U] using hmean)
  have hkSq : (u k) ^ 2 ≤ U ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_nonneg h_U] using h_u k)
  calc
    |(u k) ^ 2 - (blockEscortMean B n 1 u) ^ 2|
        ≤ |(u k) ^ 2| + |(blockEscortMean B n 1 u) ^ 2| := abs_sub _ _
    _ = (u k) ^ 2 + (blockEscortMean B n 1 u) ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    _ ≤ U ^ 2 + U ^ 2 := add_le_add hkSq hmeanSq
    _ = 2 * U ^ 2 := by ring

/-- The finite-order singular coefficient is uniformly bounded away from the
Shannon singularity on `[2, +∞)`. -/
theorem abs_singularWeight_finite_le_two {alpha : ℝ} (h_alpha : 2 ≤ alpha) :
    |singularWeight (finiteParam alpha)| ≤ 2 := by
  have hpos : 0 < alpha := by linarith
  have hone : alpha ≠ 1 := by linarith
  have hden : 0 < alpha - 1 := by linarith
  rw [singularWeight_finite hpos.le hone, abs_div, abs_of_pos hpos,
    abs_of_neg (by linarith : 1 - alpha < 0)]
  have hdeneq : -(1 - alpha) = alpha - 1 := by ring
  rw [hdeneq]
  apply (div_le_iff₀ hden).2
  nlinarith

theorem abs_blockKernelFirst_finite_large_le {J : ℕ} (B : BlockData J)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (U alpha : ℝ)
    (_h_U : 0 ≤ U) (h_u : ∀ j, |u j| ≤ U) (h_alpha : 2 ≤ alpha) :
    |blockKernelFirst B n u (finiteParam alpha)| ≤ 4 * U := by
  have hpos : 0 < alpha := by linarith
  have hone : alpha ≠ 1 := by linarith
  have hmeanAlpha := abs_blockEscortMean_le B n alpha u U h_u
  have hmeanOne := abs_blockEscortMean_le B n 1 u U h_u
  have hdiff :
      |blockEscortMean B n alpha u - blockEscortMean B n 1 u| ≤ 2 * U := by
    calc
      |blockEscortMean B n alpha u - blockEscortMean B n 1 u|
          ≤ |blockEscortMean B n alpha u| +
              |blockEscortMean B n 1 u| := abs_sub _ _
      _ ≤ U + U := add_le_add hmeanAlpha hmeanOne
      _ = 2 * U := by ring
  rw [blockKernelFirst_finite B n u hpos hone, abs_mul]
  calc
    |singularWeight (finiteParam alpha)| *
          |blockEscortMean B n alpha u - blockEscortMean B n 1 u|
        ≤ 2 * (2 * U) :=
      mul_le_mul (abs_singularWeight_finite_le_two h_alpha) hdiff
        (abs_nonneg _) (by positivity)
    _ = 4 * U := by ring

/-- Explicit finite second-kernel bound.  The only potentially growing term
is `alpha * variance`, and it is absorbed by the weighted escort tail. -/
theorem abs_blockKernelSecond_finite_large_le {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1))
    (hstrict : ∀ j : Fin (J + 1), j ≠ k → B.a j < B.a k)
    (n : ℕ) (u : Fin (J + 1) → ℝ) (U alpha : ℝ)
    (h_U : 0 ≤ U) (h_u : ∀ j, |u j| ≤ U)
    (h_alpha : max 2
      (largeAlphaInterceptBound B k / (largeAlphaSlopeGap B k / 2)) ≤ alpha) :
    |blockKernelSecond B n u (finiteParam alpha)| ≤
      4 * U ^ 2 *
          ((2 * Fintype.card (Fin (J + 1))) *
            ((largeAlphaSlopeGap B k / 2) * Real.log 2)⁻¹) +
        4 * U ^ 2 := by
  let T : ℝ := (2 * Fintype.card (Fin (J + 1))) *
    ((largeAlphaSlopeGap B k / 2) * Real.log 2)⁻¹
  let R : ℝ := ∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha
  have htwo : (2 : ℝ) ≤ alpha := (le_max_left _ _).trans h_alpha
  have hpos : 0 < alpha := by linarith
  have hone : alpha ≠ 1 := by linarith
  have hT : 0 ≤ T := by
    dsimp only [T]
    have hgap : 0 < largeAlphaSlopeGap B k / 2 := by
      have := largeAlphaSlopeGap_pos B k hstrict
      linarith
    have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact Finset.sum_nonneg fun j _ ↦ blockEscort_nonneg B n j alpha
  have halphaR : alpha * R ≤ T := by
    simpa only [R, T] using largeAlpha_mul_outside_le B k hstrict h_alpha n
  have hvar := blockEscortVar_le_outside B n alpha k u U h_U h_u
  have hvarTerm : alpha * blockEscortVar B n alpha u ≤ 4 * U ^ 2 * T := by
    calc
      alpha * blockEscortVar B n alpha u
          ≤ alpha * ((4 * U ^ 2) * R) :=
        mul_le_mul_of_nonneg_left (by simpa only [R] using hvar) hpos.le
      _ = (4 * U ^ 2) * (alpha * R) := by ring
      _ ≤ (4 * U ^ 2) * T :=
        mul_le_mul_of_nonneg_left halphaR (by positivity)
  have hmeanOne := abs_blockEscortMean_le B n 1 u U h_u
  have hmeanAlpha := abs_blockEscortMean_le B n alpha u U h_u
  have hmeanOneSq : (blockEscortMean B n 1 u) ^ 2 ≤ U ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_nonneg h_U] using hmeanOne)
  have hmeanAlphaSq : (blockEscortMean B n alpha u) ^ 2 ≤ U ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_nonneg h_U] using hmeanAlpha)
  have hsqdiff :
      |(blockEscortMean B n 1 u) ^ 2 -
          (blockEscortMean B n alpha u) ^ 2| ≤ 2 * U ^ 2 := by
    calc
      _ ≤ |(blockEscortMean B n 1 u) ^ 2| +
          |(blockEscortMean B n alpha u) ^ 2| := abs_sub _ _
      _ = (blockEscortMean B n 1 u) ^ 2 +
          (blockEscortMean B n alpha u) ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
      _ ≤ U ^ 2 + U ^ 2 := add_le_add hmeanOneSq hmeanAlphaSq
      _ = 2 * U ^ 2 := by ring
  have hsingTerm :
      |singularWeight (finiteParam alpha) *
        ((blockEscortMean B n 1 u) ^ 2 -
          (blockEscortMean B n alpha u) ^ 2)| ≤ 4 * U ^ 2 := by
    rw [abs_mul]
    calc
      |singularWeight (finiteParam alpha)| *
          |(blockEscortMean B n 1 u) ^ 2 -
            (blockEscortMean B n alpha u) ^ 2|
          ≤ 2 * (2 * U ^ 2) :=
        mul_le_mul (abs_singularWeight_finite_le_two htwo) hsqdiff
          (abs_nonneg _) (by positivity)
      _ = 4 * U ^ 2 := by ring
  rw [blockKernelSecond_finite B n u hpos hone]
  calc
    |-alpha * blockEscortVar B n alpha u +
        singularWeight (finiteParam alpha) *
          ((blockEscortMean B n 1 u) ^ 2 -
            (blockEscortMean B n alpha u) ^ 2)|
        ≤ |-alpha * blockEscortVar B n alpha u| +
          |singularWeight (finiteParam alpha) *
            ((blockEscortMean B n 1 u) ^ 2 -
              (blockEscortMean B n alpha u) ^ 2)| := abs_add_le _ _
    _ ≤ 4 * U ^ 2 * T + 4 * U ^ 2 := by
      rw [abs_mul, abs_neg, abs_of_pos hpos,
        abs_of_nonneg (blockEscortVar_nonneg B n alpha u)]
      exact add_le_add hvarTerm hsingTerm
    _ = 4 * U ^ 2 *
          ((2 * Fintype.card (Fin (J + 1))) *
            ((largeAlphaSlopeGap B k / 2) * Real.log 2)⁻¹) +
        4 * U ^ 2 := rfl

/-- Literal large-order tail package from the manuscript.  All three
constants are explicit and uniform in the scale, the order above the
threshold, and every velocity vector in the prescribed sup-norm ball. -/
theorem largeAlphaTail {J : ℕ} (B : BlockData J)
    (k : Fin (J + 1)) (U : ℝ) (h_U : 0 ≤ U)
    (hstrict : ∀ j : Fin (J + 1), j ≠ k → B.a j < B.a k) :
    ∃ A gamma C : ℝ,
      1 < A ∧ 0 < gamma ∧ 0 ≤ C ∧
      ∀ (n : ℕ) (alpha : ℝ) (u : Fin (J + 1) → ℝ),
        A ≤ alpha → (∀ j, |u j| ≤ U) →
          (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha ≤
              C * Real.rpow (blockScale n) (-gamma * alpha)) ∧
          (alpha * (∑ j ∈ Finset.univ.erase k,
              blockEscort B n j alpha) ≤ C) ∧
          (|blockKernelFirst B n u (finiteParam alpha)| ≤ C) ∧
          (|blockKernelSecond B n u (finiteParam alpha)| ≤ C) ∧
          (|blockKernelFirst B n u ⊤| ≤ C) ∧
          (|blockKernelSecond B n u ⊤| ≤ C) := by
  let delta := largeAlphaSlopeGap B k
  let gamma := delta / 2
  let M := largeAlphaInterceptBound B k
  let A := max 2 (M / gamma)
  let N : ℝ := 2 * Fintype.card (Fin (J + 1))
  let T : ℝ := N * (gamma * Real.log 2)⁻¹
  let C : ℝ := N + T + 4 * U + (4 * U ^ 2 * T + 4 * U ^ 2) +
    2 * U + 2 * U ^ 2
  have hdelta : 0 < delta := by
    simpa only [delta] using largeAlphaSlopeGap_pos B k hstrict
  have hgamma : 0 < gamma := by dsimp only [gamma]; linarith
  have hA : 1 < A := by
    have htwo : (2 : ℝ) ≤ A := by
      dsimp only [A]
      exact le_max_left _ _
    linarith
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have h4U : 0 ≤ 4 * U := by positivity
  have h4U2T : 0 ≤ 4 * U ^ 2 * T := by positivity
  have h4U2 : 0 ≤ 4 * U ^ 2 := by positivity
  have h2U : 0 ≤ 2 * U := by positivity
  have h2U2 : 0 ≤ 2 * U ^ 2 := by positivity
  have hNC : N ≤ C := by dsimp only [C]; linarith
  have hTC : T ≤ C := by dsimp only [C]; linarith
  have hFirstC : 4 * U ≤ C := by dsimp only [C]; linarith
  have hSecondC : 4 * U ^ 2 * T + 4 * U ^ 2 ≤ C := by
    dsimp only [C]
    linarith
  have hTopFirstC : 2 * U ≤ C := by dsimp only [C]; linarith
  have hTopSecondC : 2 * U ^ 2 ≤ C := by dsimp only [C]; linarith
  refine ⟨A, gamma, C, hA, hgamma, hC, ?_⟩
  intro n alpha u h_alpha hu
  have hthreshold : max 2
      (largeAlphaInterceptBound B k / (largeAlphaSlopeGap B k / 2)) ≤ alpha := by
    simpa only [A, M, gamma, delta] using h_alpha
  have htwo : (2 : ℝ) ≤ alpha := (le_max_left _ _).trans hthreshold
  have hrpow : 0 ≤ Real.rpow (blockScale n) (-gamma * alpha) :=
    Real.rpow_nonneg (blockScale_pos n).le _
  have hout := largeAlpha_outside_le B k hstrict hthreshold n
  have houtC :
      ∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha ≤
        C * Real.rpow (blockScale n) (-gamma * alpha) := by
    calc
      _ ≤ N * Real.rpow (blockScale n) (-gamma * alpha) := by
        simpa only [N, gamma, delta] using hout
      _ ≤ C * Real.rpow (blockScale n) (-gamma * alpha) :=
        mul_le_mul_of_nonneg_right hNC hrpow
  have hmul := largeAlpha_mul_outside_le B k hstrict hthreshold n
  have hmulC :
      alpha * (∑ j ∈ Finset.univ.erase k, blockEscort B n j alpha) ≤ C := by
    calc
      _ ≤ T := by simpa only [T, N, gamma, delta] using hmul
      _ ≤ C := hTC
  have hfirst := abs_blockKernelFirst_finite_large_le B n u U alpha h_U hu htwo
  have hfirstC : |blockKernelFirst B n u (finiteParam alpha)| ≤ C :=
    hfirst.trans hFirstC
  have hsecond := abs_blockKernelSecond_finite_large_le B k hstrict n u U alpha
    h_U hu hthreshold
  have hsecondC : |blockKernelSecond B n u (finiteParam alpha)| ≤ C := by
    calc
      _ ≤ 4 * U ^ 2 * T + 4 * U ^ 2 := by
        simpa only [T, N, gamma, delta] using hsecond
      _ ≤ C := hSecondC
  have htopFirst := abs_blockKernelFirst_top_le B k hstrict n u U hu
  have htopSecond := abs_blockKernelSecond_top_le B k hstrict n u U h_U hu
  exact ⟨houtC, hmulC, hfirstC, hsecondC,
    htopFirst.trans hTopFirstC, htopSecond.trans hTopSecondC⟩

end LargeAlpha

end ConditionalEntropy
