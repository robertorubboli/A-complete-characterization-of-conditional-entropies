import ConditionalEntropy.CompactUniform
import ConditionalEntropy.ShannonCurves
import ConditionalEntropy.ShannonDominance
import ConditionalEntropy.ShannonEscortCalculus

/-!
# Uniform logarithmic-mass estimates for the Shannon family

This module proves the logarithmic-mass clause used by the dedicated Shannon
localization.  Its public theorem is the literal four-part package from the
manuscript: two compact-uniform limits, one quantitative first-derivative
bound, and the exact square identity for the second derivative.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace ConditionalEntropy

private def shannonLogMassDecay (theta : ShannonData) (n : ℕ) : ℝ :=
  Real.rpow (blockScale n) (1 - theta.R) / Real.log (blockScale n) +
    Real.rpow (blockScale n) (1 - theta.c)

private theorem shannonLogMassDecay_nonneg (theta : ShannonData) (n : ℕ) :
    0 ≤ shannonLogMassDecay theta n := by
  unfold shannonLogMassDecay
  exact add_nonneg
    (div_nonneg (Real.rpow_nonneg (blockScale_pos n).le _)
      (Real.log_pos (by
        change 1 < (n : ℝ) + 2
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith)).le)
    (Real.rpow_nonneg (blockScale_pos n).le _)

private theorem compactUniformError_zero_bounds
    {U : Type*} (K : Set U) (hK0 : K.Nonempty)
    (f : ℕ → U → ℝ) (n : ℕ) (B : ℝ)
    (hB : ∀ x ∈ K, |f n x| ≤ B) :
    0 ≤ compactUniformError K f (fun _ ↦ 0) n ∧
      compactUniformError K f (fun _ ↦ 0) n ≤ B := by
  unfold compactUniformError
  obtain ⟨x, hx⟩ := hK0
  have hmem : |f n x - 0| ∈
      {r : ℝ | ∃ y ∈ K, r = |f n y - 0|} :=
    ⟨x, hx, rfl⟩
  have hbdd : BddAbove {r : ℝ | ∃ y ∈ K, r = |f n y - 0|} := by
    refine ⟨B, ?_⟩
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    simpa using hB y hy
  constructor
  · exact (abs_nonneg (f n x - 0)).trans (le_csSup hbdd hmem)
  · apply csSup_le
    · exact ⟨|f n x - 0|, hmem⟩
    · intro r hr
      rcases hr with ⟨y, hy, rfl⟩
      simpa using hB y hy

private theorem exists_compact_pair_abs_bound (K : Set (ℝ × ℝ))
    (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, |z.1| ≤ B ∧ |z.2| ≤ B := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ × ℝ)
  let B := max R 0
  have hB : 0 ≤ B := le_max_right R 0
  refine ⟨B, hB, ?_⟩
  intro z hz
  have hzBall := hR hz
  have hznorm : ‖z‖ ≤ R := by
    simpa [dist_zero_right] using hzBall
  constructor
  · calc
      |z.1| = ‖z.1‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖z‖ := norm_fst_le z
      _ ≤ R := hznorm
      _ ≤ B := le_max_left R 0
  · calc
      |z.2| = ‖z.2‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖z‖ := norm_snd_le z
      _ ≤ R := hznorm
      _ ≤ B := le_max_left R 0

private theorem abs_shannonCount_cancellation_le (theta : ShannonData)
    (n : ℕ) :
    |(shannonCount theta n 0 : ℝ) -
        shannonScale n * (shannonCount theta n 1 : ℝ)| ≤
      1 + shannonScale n := by
  let d := shannonScale n
  have hd : 0 < d := shannonScale_pos n
  have hpow : Real.rpow d theta.R =
      d * Real.rpow d (theta.R - 1) := by
    calc
      Real.rpow d theta.R =
          Real.rpow d (1 + (theta.R - 1)) := by
            congr 1
            ring
      _ = Real.rpow d 1 * Real.rpow d (theta.R - 1) := by
        change d ^ (1 + (theta.R - 1)) =
          d ^ (1 : ℝ) * d ^ (theta.R - 1)
        exact Real.rpow_add hd 1 (theta.R - 1)
      _ = d * Real.rpow d (theta.R - 1) := by
        change d ^ (1 : ℝ) * d ^ (theta.R - 1) =
          d * d ^ (theta.R - 1)
        rw [Real.rpow_one]
  have h0lo : Real.rpow d theta.R ≤
      (Nat.ceil (Real.rpow d theta.R) : ℝ) := Nat.le_ceil _
  have h0hi : (Nat.ceil (Real.rpow d theta.R) : ℝ) ≤
      Real.rpow d theta.R + 1 :=
    (Nat.ceil_lt_add_one (Real.rpow_nonneg hd.le _)).le
  have h1lo : Real.rpow d (theta.R - 1) ≤
      (Nat.ceil (Real.rpow d (theta.R - 1)) : ℝ) := Nat.le_ceil _
  have h1hi : (Nat.ceil (Real.rpow d (theta.R - 1)) : ℝ) ≤
      Real.rpow d (theta.R - 1) + 1 :=
    (Nat.ceil_lt_add_one (Real.rpow_nonneg hd.le _)).le
  have h1lo' := mul_le_mul_of_nonneg_left h1lo hd.le
  have h1hi' := mul_le_mul_of_nonneg_left h1hi hd.le
  change |(Nat.ceil (Real.rpow d theta.R) : ℝ) -
      d * (Nat.ceil (Real.rpow d (theta.R - 1)) : ℝ)| ≤ 1 + d
  rw [abs_le]
  constructor <;> nlinarith

private theorem shannonThird_scaled_count_le (theta : ShannonData)
    (n : ℕ) :
    shannonScale n ^ 2 * (shannonCount theta n 2 : ℝ) ≤
      Real.rpow (shannonScale n) (theta.R + 1 - theta.c) +
        shannonScale n ^ 2 := by
  let d := shannonScale n
  have hd : 0 < d := shannonScale_pos n
  have hceil : (Nat.ceil (Real.rpow d (theta.R - 1 - theta.c)) : ℝ) ≤
      Real.rpow d (theta.R - 1 - theta.c) + 1 :=
    (Nat.ceil_lt_add_one (Real.rpow_nonneg hd.le _)).le
  have hmul := mul_le_mul_of_nonneg_left hceil (sq_nonneg d)
  have hpow : d ^ 2 * Real.rpow d (theta.R - 1 - theta.c) =
      Real.rpow d (theta.R + 1 - theta.c) := by
    calc
      d ^ 2 * Real.rpow d (theta.R - 1 - theta.c) =
          Real.rpow d (2 : ℝ) *
            Real.rpow d (theta.R - 1 - theta.c) := by
              rw [show d ^ 2 = Real.rpow d (2 : ℝ) by
                symm
                exact Real.rpow_natCast d 2]
      _ = Real.rpow d ((2 : ℝ) + (theta.R - 1 - theta.c)) := by
        change d ^ (2 : ℝ) * d ^ (theta.R - 1 - theta.c) =
          d ^ (2 + (theta.R - 1 - theta.c))
        exact (Real.rpow_add hd 2 (theta.R - 1 - theta.c)).symm
      _ = Real.rpow d (theta.R + 1 - theta.c) := by
        congr 1
        ring
  change d ^ 2 *
      (Nat.ceil (Real.rpow d (theta.R - 1 - theta.c)) : ℝ) ≤
    Real.rpow d (theta.R + 1 - theta.c) + d ^ 2
  rw [← hpow]
  nlinarith

@[simp] private theorem shannonContribution_zero_one
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) :
    shannonContribution theta n z 0 1 =
      (shannonCount theta n 0 : ℝ) * theta.q := by
  simp [shannonContribution, shannonBase, shannonRepresentative,
    Real.rpow_one]

@[simp] private theorem shannonContribution_one_one
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) :
    shannonContribution theta n z 1 1 =
      (shannonCount theta n 1 : ℝ) * (shannonScale n * theta.p) := by
  simp [shannonContribution, shannonBase, shannonRepresentative,
    Real.rpow_one]

@[simp] private theorem shannonContribution_two_one
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) :
    shannonContribution theta n z 2 1 =
      (shannonCount theta n 2 : ℝ) * shannonScale n ^ 2 := by
  simp [shannonContribution, shannonBase, shannonRepresentative,
    Real.rpow_one]

private theorem shannonMean_one_eq_rounding_numerator
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) :
    shannonMean theta n z 1 =
      (z.1 / shannonLogScale n *
          ((shannonCount theta n 0 : ℝ) -
            shannonScale n * (shannonCount theta n 1 : ℝ)) +
        z.2 * shannonScale n ^ 2 *
          (shannonCount theta n 2 : ℝ)) /
        (∑ j : Fin 3, shannonContribution theta n z j 1) := by
  have hden :
      shannonContribution theta n z 0 1 +
          shannonContribution theta n z 1 1 +
          shannonContribution theta n z 2 1 ≠ 0 := by
    have hpos := sum_shannonContribution_pos theta n z 1
    simpa only [Fin.sum_univ_three] using hpos.ne'
  unfold shannonMean shannonEscort
  simp only [Fin.sum_univ_three, shannonContribution_zero_one,
    shannonContribution_one_one, shannonContribution_two_one,
    shannonBlockVelocity_zero, shannonBlockVelocity_one,
    shannonBlockVelocity_two]
  field_simp [hden, theta.q_pos.ne', theta.p_pos.ne',
    (shannonLogScale_pos n).ne']
  ring

private theorem shannonContributionSum_lower (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) :
    theta.q * Real.rpow (shannonScale n) theta.R ≤
      ∑ j : Fin 3, shannonContribution theta n z j 1 := by
  have hzero := shannonIdeal_le_contribution theta n z 0 1
  have hzero' : theta.q * Real.rpow (shannonScale n) theta.R ≤
      shannonContribution theta n z 0 1 := by
    simpa [shannonPrefactor_zero, shannonExponent_zero,
      Real.rpow_one] using hzero
  exact hzero'.trans <| Finset.single_le_sum
    (fun j _hj ↦ (shannonContribution_pos theta n z j 1).le)
    (Finset.mem_univ 0)

private theorem shannonLogMassKernel_one_bound
    (theta : ShannonData) (K : Set (ℝ × ℝ)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ z ∈ K,
      |shannonLogMassKernel theta n z 1| ≤
        C * shannonLogMassDecay theta n := by
  obtain ⟨B, hB, hcoord⟩ := exists_compact_pair_abs_bound K hK
  let C := 2 * B / theta.q
  have hC : 0 ≤ C := div_nonneg (mul_nonneg (by norm_num) hB) theta.q_pos.le
  refine ⟨C, hC, ?_⟩
  intro n z hz
  have hz1 := (hcoord z hz).1
  have hz2 := (hcoord z hz).2
  let d := shannonScale n
  let L := shannonLogScale n
  let dR := Real.rpow d theta.R
  let S := ∑ j : Fin 3, shannonContribution theta n z j 1
  let A := z.1 / L *
      ((shannonCount theta n 0 : ℝ) -
        d * (shannonCount theta n 1 : ℝ)) +
    z.2 * d ^ 2 * (shannonCount theta n 2 : ℝ)
  have hd : 0 < d := shannonScale_pos n
  have hd1 : 1 ≤ d := (one_lt_shannonScale n).le
  have hL : 0 < L := shannonLogScale_pos n
  have hdR : 0 < dR := Real.rpow_pos_of_pos hd theta.R
  have hS : 0 < S := by
    dsimp only [S]
    exact sum_shannonContribution_pos theta n z 1
  have hcancel :
      |(shannonCount theta n 0 : ℝ) -
          d * (shannonCount theta n 1 : ℝ)| ≤ 1 + d := by
    simpa only [d] using abs_shannonCount_cancellation_le theta n
  have hthird : d ^ 2 * (shannonCount theta n 2 : ℝ) ≤
      Real.rpow d (theta.R + 1 - theta.c) + d ^ 2 := by
    simpa only [d] using shannonThird_scaled_count_le theta n
  have hfirstTerm :
      |z.1 / L *
          ((shannonCount theta n 0 : ℝ) -
            d * (shannonCount theta n 1 : ℝ))| ≤
        B / L * (1 + d) := by
    rw [abs_mul, abs_div, abs_of_pos hL]
    exact mul_le_mul
      (div_le_div_of_nonneg_right hz1 hL.le) hcancel
      (abs_nonneg _) (div_nonneg hB hL.le)
  have hthirdNonneg :
      0 ≤ d ^ 2 * (shannonCount theta n 2 : ℝ) :=
    mul_nonneg (sq_nonneg d) (Nat.cast_nonneg _)
  have hthirdRhsNonneg :
      0 ≤ Real.rpow d (theta.R + 1 - theta.c) + d ^ 2 :=
    add_nonneg (Real.rpow_nonneg hd.le _) (sq_nonneg d)
  have hthirdTerm :
      |z.2 * d ^ 2 * (shannonCount theta n 2 : ℝ)| ≤
        B * (Real.rpow d (theta.R + 1 - theta.c) + d ^ 2) := by
    rw [mul_assoc, abs_mul, abs_of_nonneg hthirdNonneg]
    calc
      |z.2| * (d ^ 2 * (shannonCount theta n 2 : ℝ)) ≤
          B * (d ^ 2 * (shannonCount theta n 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hz2 hthirdNonneg
      _ ≤ B * (Real.rpow d (theta.R + 1 - theta.c) + d ^ 2) :=
        mul_le_mul_of_nonneg_left hthird hB
  have hA : |A| ≤
      B / L * (1 + d) +
        B * (Real.rpow d (theta.R + 1 - theta.c) + d ^ 2) := by
    dsimp only [A]
    exact (abs_add_le _ _).trans (add_le_add hfirstTerm hthirdTerm)
  have hdTwo : d ^ 2 ≤ Real.rpow d (theta.R + 1 - theta.c) := by
    have hexp : (2 : ℝ) ≤ theta.R + 1 - theta.c := by
      linarith [theta.R_gt]
    have hr := Real.rpow_le_rpow_of_exponent_le hd1 hexp
    calc
      d ^ 2 = Real.rpow d (2 : ℝ) := (Real.rpow_natCast d 2).symm
      _ ≤ Real.rpow d (theta.R + 1 - theta.c) := hr
  have hRpow :
      dR * Real.rpow d (1 - theta.R) = d := by
    dsimp only [dR]
    calc
      Real.rpow d theta.R * Real.rpow d (1 - theta.R) =
          Real.rpow d (theta.R + (1 - theta.R)) := by
            change d ^ theta.R * d ^ (1 - theta.R) =
              d ^ (theta.R + (1 - theta.R))
            exact (Real.rpow_add hd theta.R (1 - theta.R)).symm
      _ = d := by
        rw [show theta.R + (1 - theta.R) = 1 by ring]
        change d ^ (1 : ℝ) = d
        rw [Real.rpow_one]
  have hCpow :
      dR * Real.rpow d (1 - theta.c) =
        Real.rpow d (theta.R + 1 - theta.c) := by
    dsimp only [dR]
    calc
      Real.rpow d theta.R * Real.rpow d (1 - theta.c) =
          Real.rpow d (theta.R + (1 - theta.c)) := by
            change d ^ theta.R * d ^ (1 - theta.c) =
              d ^ (theta.R + (1 - theta.c))
            exact (Real.rpow_add hd theta.R (1 - theta.c)).symm
      _ = Real.rpow d (theta.R + 1 - theta.c) := by
        congr 1
        ring
  have hlarge :
      B / L * (1 + d) +
          B * (Real.rpow d (theta.R + 1 - theta.c) + d ^ 2) ≤
        2 * B * dR *
          (Real.rpow d (1 - theta.R) / L +
            Real.rpow d (1 - theta.c)) := by
    calc
      B / L * (1 + d) +
          B * (Real.rpow d (theta.R + 1 - theta.c) + d ^ 2) ≤
        B / L * (2 * d) +
          B * (2 * Real.rpow d (theta.R + 1 - theta.c)) := by
            apply add_le_add
            · apply mul_le_mul_of_nonneg_left
                (by linarith : 1 + d ≤ 2 * d)
                (div_nonneg hB hL.le)
            · apply mul_le_mul_of_nonneg_left _ hB
              linarith
      _ = 2 * B * dR *
          (Real.rpow d (1 - theta.R) / L +
            Real.rpow d (1 - theta.c)) := by
            symm
            calc
              2 * B * dR *
                    (Real.rpow d (1 - theta.R) / L +
                      Real.rpow d (1 - theta.c)) =
                  2 * B *
                    ((dR * Real.rpow d (1 - theta.R)) / L +
                      dR * Real.rpow d (1 - theta.c)) := by ring
              _ = 2 * B * (d / L +
                    Real.rpow d (theta.R + 1 - theta.c)) := by
                  rw [hRpow, hCpow]
              _ = B / L * (2 * d) +
                    B * (2 * Real.rpow d
                      (theta.R + 1 - theta.c)) := by ring
  have hden : theta.q * dR ≤ S := by
    dsimp only [dR, S]
    exact shannonContributionSum_lower theta n z
  have hdenPos : 0 < theta.q * dR := mul_pos theta.q_pos hdR
  have hbigNonneg :
      0 ≤ 2 * B * dR *
        (Real.rpow d (1 - theta.R) / L +
          Real.rpow d (1 - theta.c)) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hB) hdR.le)
      (add_nonneg
        (div_nonneg (Real.rpow_nonneg hd.le _) hL.le)
        (Real.rpow_nonneg hd.le _))
  rw [shannonLogMassKernel_one, shannonMean_one_eq_rounding_numerator]
  change |A / S| ≤ C * shannonLogMassDecay theta n
  rw [abs_div, abs_of_pos hS]
  calc
    |A| / S ≤
        (2 * B * dR *
          (Real.rpow d (1 - theta.R) / L +
            Real.rpow d (1 - theta.c))) / S :=
      div_le_div_of_nonneg_right (hA.trans hlarge) hS.le
    _ ≤ (2 * B * dR *
          (Real.rpow d (1 - theta.R) / L +
            Real.rpow d (1 - theta.c))) / (theta.q * dR) :=
      div_le_div_of_nonneg_left hbigNonneg hdenPos hden
    _ = C * shannonLogMassDecay theta n := by
      dsimp only [C, shannonLogMassDecay, d, L, dR]
      unfold shannonLogScale shannonScale
      field_simp [theta.q_pos.ne',
        (Real.rpow_pos_of_pos (blockScale_pos n) theta.R).ne',
        (shannonLogScale_pos n).ne']

private theorem tendsto_shannonLogMassDecay (theta : ShannonData) :
    Tendsto (shannonLogMassDecay theta) atTop (𝓝 0) := by
  have hR : 0 < theta.R - 1 := by
    linarith [theta.R_gt, theta.c_gt_one]
  have hc : 0 < theta.c - 1 := by linarith [theta.c_gt_one]
  have hpowR : Tendsto
      (fun n : ℕ ↦ Real.rpow (blockScale n) (1 - theta.R))
      atTop (𝓝 0) := by
    have hbase : Tendsto
        (fun n : ℕ ↦ Real.rpow (blockScale n) (-(theta.R - 1)))
        atTop (𝓝 0) := by
      exact (tendsto_rpow_neg_atTop hR).comp tendsto_blockScale_atTop
    simpa only [show 1 - theta.R = -(theta.R - 1) by ring] using hbase
  have hpowC : Tendsto
      (fun n : ℕ ↦ Real.rpow (blockScale n) (1 - theta.c))
      atTop (𝓝 0) := by
    have hbase : Tendsto
        (fun n : ℕ ↦ Real.rpow (blockScale n) (-(theta.c - 1)))
        atTop (𝓝 0) := by
      exact (tendsto_rpow_neg_atTop hc).comp tendsto_blockScale_atTop
    simpa only [show 1 - theta.c = -(theta.c - 1) by ring] using hbase
  have hdiv : Tendsto
      (fun n : ℕ ↦ Real.rpow (blockScale n) (1 - theta.R) /
        Real.log (blockScale n)) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact div_nonneg (Real.rpow_nonneg (blockScale_pos n).le _)
        (Real.log_pos (by
          change 1 < (n : ℝ) + 2
          have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith)).le
    · intro n
      have hlog : Real.log (2 : ℝ) ≤ Real.log (blockScale n) := by
        simpa only [shannonLogScale, shannonScale] using
          log_two_le_shannonLogScale n
      exact div_le_div_of_nonneg_left
        (Real.rpow_nonneg (blockScale_pos n).le _)
        log_two_pos hlog
    · have hconst : Tendsto
          (fun _ : ℕ ↦ (Real.log (2 : ℝ))⁻¹) atTop
          (𝓝 (Real.log (2 : ℝ))⁻¹) := tendsto_const_nhds
      simpa only [div_eq_mul_inv, zero_mul] using hpowR.mul hconst
  unfold shannonLogMassDecay
  simpa only [zero_add] using hdiv.add hpowC

/-- The logarithmic Shannon mass has vanishing first and second derivatives,
uniformly on compact direction sets, together with the quantitative bound and
the exact square identity used by Shannon localization. -/
theorem shannonLogMass (theta : ShannonData) (K : Set (ℝ × ℝ))
    (hK0 : K.Nonempty) (hK : IsCompact K) :
    Tendsto
        (fun n ↦ compactUniformError K
          (fun m z ↦ shannonLogMassKernel theta m z 1)
          (fun _ ↦ 0) n)
        atTop (𝓝 0) ∧
      Tendsto
        (fun n ↦ compactUniformError K
          (fun m z ↦ shannonLogMassKernel theta m z 2)
          (fun _ ↦ 0) n)
        atTop (𝓝 0) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ z : ℝ × ℝ, z ∈ K →
        |shannonLogMassKernel theta n z 1| ≤
          C * (Real.rpow (blockScale n) (1 - theta.R) /
              Real.log (blockScale n) +
            Real.rpow (blockScale n) (1 - theta.c)) ∧
        shannonLogMassKernel theta n z 2 =
          -shannonLogMassKernel theta n z 1 ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := shannonLogMassKernel_one_bound theta K hK
  have hdecay := tendsto_shannonLogMassDecay theta
  have hCdecay : Tendsto (fun n ↦ C * shannonLogMassDecay theta n)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdecay
  have hfirst : Tendsto
      (fun n ↦ compactUniformError K
        (fun m z ↦ shannonLogMassKernel theta m z 1)
        (fun _ ↦ 0) n) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact (compactUniformError_zero_bounds K hK0
        (fun m z ↦ shannonLogMassKernel theta m z 1) n
        (C * shannonLogMassDecay theta n) (hbound n)).1
    · intro n
      exact (compactUniformError_zero_bounds K hK0
        (fun m z ↦ shannonLogMassKernel theta m z 1) n
        (C * shannonLogMassDecay theta n) (hbound n)).2
    · exact hCdecay
  have hsecondPoint : ∀ n : ℕ, ∀ z ∈ K,
      |shannonLogMassKernel theta n z 2| ≤
        (C * shannonLogMassDecay theta n) ^ 2 := by
    intro n z hz
    rw [shannonLogMassKernel_two_eq_neg_sq, abs_neg, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (hbound n z hz) 2
  have hsecondMajorant : Tendsto
      (fun n ↦ (C * shannonLogMassDecay theta n) ^ 2)
      atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      hCdecay.pow 2
  have hsecond : Tendsto
      (fun n ↦ compactUniformError K
        (fun m z ↦ shannonLogMassKernel theta m z 2)
        (fun _ ↦ 0) n) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact (compactUniformError_zero_bounds K hK0
        (fun m z ↦ shannonLogMassKernel theta m z 2) n
        ((C * shannonLogMassDecay theta n) ^ 2)
        (hsecondPoint n)).1
    · intro n
      exact (compactUniformError_zero_bounds K hK0
        (fun m z ↦ shannonLogMassKernel theta m z 2) n
        ((C * shannonLogMassDecay theta n) ^ 2)
        (hsecondPoint n)).2
    · exact hsecondMajorant
  refine ⟨hfirst, hsecond, C, hC, ?_⟩
  intro n z hz
  constructor
  · simpa only [shannonLogMassDecay] using hbound n z hz
  · exact shannonLogMassKernel_two_eq_neg_sq theta n z

end ConditionalEntropy
