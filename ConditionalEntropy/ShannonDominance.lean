import ConditionalEntropy.ShannonEscortCalculus

/-!
# Quantitative dominance for the dedicated Shannon blocks

The fixed factors `theta.p` and `theta.q` prevent the Shannon family from
being a literal instance of `BlockData`.  This file records the corresponding
ideal exponent and prefactor, proves the same factor-two rounding comparison,
and packages the compact prefactor bound needed by every dominant-region
argument.
-/

noncomputable section

open Filter Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

/-- The exponent supplied by the rounded cardinality of a Shannon block. -/
def shannonCountExponent (theta : ShannonData) (j : Fin 3) : ℝ :=
  match j.1 with
  | 0 => theta.R
  | 1 => theta.R - 1
  | _ => theta.R - 1 - theta.c

/-- Scale amplitude of the three Shannon bases. -/
def shannonAmplitude (j : Fin 3) : ℝ :=
  match j.1 with
  | 0 => 0
  | 1 => 1
  | _ => 2

/-- The affine scale exponent of a Shannon power-sum contribution. -/
def shannonExponent (theta : ShannonData) (j : Fin 3) (alpha : ℝ) : ℝ :=
  shannonCountExponent theta j + shannonAmplitude j * alpha

/-- The scale-free factor in a Shannon power-sum contribution. -/
def shannonPrefactor (theta : ShannonData) (j : Fin 3) (alpha : ℝ) : ℝ :=
  match j.1 with
  | 0 => Real.rpow theta.q alpha
  | 1 => Real.rpow theta.p alpha
  | _ => 1

@[simp] theorem shannonExponent_zero (theta : ShannonData) (alpha : ℝ) :
    shannonExponent theta 0 alpha = theta.R := by
  simp [shannonExponent, shannonCountExponent, shannonAmplitude]

@[simp] theorem shannonExponent_one (theta : ShannonData) (alpha : ℝ) :
    shannonExponent theta 1 alpha = theta.R - 1 + alpha := by
  simp [shannonExponent, shannonCountExponent, shannonAmplitude]

@[simp] theorem shannonExponent_two (theta : ShannonData) (alpha : ℝ) :
    shannonExponent theta 2 alpha = theta.R - 1 - theta.c + 2 * alpha := by
  simp [shannonExponent, shannonCountExponent, shannonAmplitude]

@[simp] theorem shannonPrefactor_zero (theta : ShannonData) (alpha : ℝ) :
    shannonPrefactor theta 0 alpha = Real.rpow theta.q alpha := by
  simp [shannonPrefactor]

@[simp] theorem shannonPrefactor_one (theta : ShannonData) (alpha : ℝ) :
    shannonPrefactor theta 1 alpha = Real.rpow theta.p alpha := by
  simp [shannonPrefactor]

@[simp] theorem shannonPrefactor_two (theta : ShannonData) (alpha : ℝ) :
    shannonPrefactor theta 2 alpha = 1 := by
  simp [shannonPrefactor]

theorem shannonCountExponent_pos (theta : ShannonData) (j : Fin 3) :
    0 < shannonCountExponent theta j := by
  fin_cases j
  · change 0 < theta.R
    linarith [theta.R_gt, theta.c_gt_one]
  · change 0 < theta.R - 1
    linarith [theta.R_gt, theta.c_gt_one]
  · change 0 < theta.R - 1 - theta.c
    linarith [theta.R_gt]

theorem shannonPrefactor_pos (theta : ShannonData) (j : Fin 3)
    (alpha : ℝ) : 0 < shannonPrefactor theta j alpha := by
  fin_cases j
  · change 0 < Real.rpow theta.q alpha
    exact Real.rpow_pos_of_pos theta.q_pos alpha
  · change 0 < Real.rpow theta.p alpha
    exact Real.rpow_pos_of_pos theta.p_pos alpha
  · change 0 < (1 : ℝ)
    norm_num

theorem continuous_shannonPrefactor (theta : ShannonData) (j : Fin 3) :
    Continuous (shannonPrefactor theta j) := by
  fin_cases j
  · change Continuous (fun alpha : ℝ ↦ Real.rpow theta.q alpha)
    exact Real.continuous_const_rpow theta.q_pos.ne'
  · change Continuous (fun alpha : ℝ ↦ Real.rpow theta.p alpha)
    exact Real.continuous_const_rpow theta.p_pos.ne'
  · change Continuous (fun _alpha : ℝ ↦ (1 : ℝ))
    exact continuous_const

/-- The unrounded power lies below its rounded Shannon cardinality. -/
theorem rpow_shannonCountExponent_le_count (theta : ShannonData) (n : ℕ)
    (j : Fin 3) :
    Real.rpow (shannonScale n) (shannonCountExponent theta j) ≤
      (shannonCount theta n j : ℝ) := by
  fin_cases j <;> exact Nat.le_ceil _

/-- Ceiling rounding costs at most a factor two in every Shannon block. -/
theorem shannonCount_le_two_mul_rpow (theta : ShannonData) (n : ℕ)
    (j : Fin 3) :
    (shannonCount theta n j : ℝ) ≤
      2 * Real.rpow (shannonScale n) (shannonCountExponent theta j) := by
  have hxpos : 0 < Real.rpow (shannonScale n)
      (shannonCountExponent theta j) :=
    Real.rpow_pos_of_pos (shannonScale_pos n) _
  have hxone : 1 ≤ Real.rpow (shannonScale n)
      (shannonCountExponent theta j) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le (one_lt_shannonScale n).le
        (shannonCountExponent_pos theta j).le
  calc
    (shannonCount theta n j : ℝ) ≤
        Real.rpow (shannonScale n) (shannonCountExponent theta j) + 1 := by
      fin_cases j <;> exact (Nat.ceil_lt_add_one hxpos.le).le
    _ ≤ 2 * Real.rpow (shannonScale n)
        (shannonCountExponent theta j) := by linarith

/-- Exact factorization of a Shannon contribution into a rounded count,
scale-free prefactor, and a pure scale power. -/
theorem shannonContribution_factorization (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (j : Fin 3) (alpha : ℝ) :
    shannonContribution theta n z j alpha =
      (shannonCount theta n j : ℝ) * shannonPrefactor theta j alpha *
        Real.rpow (shannonScale n)
          (shannonAmplitude j * alpha) := by
  have hd := (shannonScale_pos n).le
  fin_cases j
  · change (shannonCount theta n 0 : ℝ) * Real.rpow theta.q alpha =
      (shannonCount theta n 0 : ℝ) * Real.rpow theta.q alpha *
        Real.rpow (shannonScale n) (0 * alpha)
    simp only [zero_mul]
    simp only [Real.rpow_eq_pow] at *
    rw [Real.rpow_zero, mul_one]
  · change (shannonCount theta n 1 : ℝ) *
      Real.rpow (shannonScale n * theta.p) alpha =
        (shannonCount theta n 1 : ℝ) * Real.rpow theta.p alpha *
          Real.rpow (shannonScale n) (1 * alpha)
    rw [one_mul]
    simp only [Real.rpow_eq_pow] at *
    rw [Real.mul_rpow (shannonScale_pos n).le theta.p_pos.le]
    ring
  · change (shannonCount theta n 2 : ℝ) *
      Real.rpow (shannonScale n ^ 2) alpha =
        (shannonCount theta n 2 : ℝ) * 1 *
          Real.rpow (shannonScale n) (2 * alpha)
    rw [show shannonScale n ^ 2 =
      Real.rpow (shannonScale n) (2 : ℝ) by
        symm
        exact Real.rpow_natCast (shannonScale n) 2]
    simp only [Real.rpow_eq_pow] at *
    rw [Real.rpow_mul hd (2 : ℝ) alpha]
    ring

/-- The prefactor times the ideal affine scale power is a lower bound for
the rounded Shannon contribution. -/
theorem shannonIdeal_le_contribution (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (j : Fin 3) (alpha : ℝ) :
    shannonPrefactor theta j alpha *
        Real.rpow (shannonScale n) (shannonExponent theta j alpha) ≤
      shannonContribution theta n z j alpha := by
  let a : ℝ := shannonAmplitude j
  let m := shannonCountExponent theta j
  let P := shannonPrefactor theta j alpha
  have hd := shannonScale_pos n
  have hP : 0 ≤ P := (shannonPrefactor_pos theta j alpha).le
  have ha : 0 ≤ Real.rpow (shannonScale n) (a * alpha) :=
    Real.rpow_nonneg hd.le _
  rw [shannonContribution_factorization]
  change P * Real.rpow (shannonScale n) (m + a * alpha) ≤
    (shannonCount theta n j : ℝ) * P *
      Real.rpow (shannonScale n) (a * alpha)
  simp only [Real.rpow_eq_pow] at *
  rw [Real.rpow_add hd]
  have hc := rpow_shannonCountExponent_le_count theta n j
  change Real.rpow (shannonScale n) m ≤
    (shannonCount theta n j : ℝ) at hc
  have hmul := mul_le_mul_of_nonneg_right hc (mul_nonneg hP ha)
  calc
    P * (Real.rpow (shannonScale n) m *
        Real.rpow (shannonScale n) (a * alpha)) =
      Real.rpow (shannonScale n) m *
        (P * Real.rpow (shannonScale n) (a * alpha)) := by ring
    _ ≤ (shannonCount theta n j : ℝ) *
        (P * Real.rpow (shannonScale n) (a * alpha)) := hmul
    _ = (shannonCount theta n j : ℝ) * P *
        Real.rpow (shannonScale n) (a * alpha) := by ring

/-- The rounded Shannon contribution is at most twice its ideal value. -/
theorem shannonContribution_le_two_mul_ideal (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (j : Fin 3) (alpha : ℝ) :
    shannonContribution theta n z j alpha ≤
      2 * (shannonPrefactor theta j alpha *
        Real.rpow (shannonScale n) (shannonExponent theta j alpha)) := by
  let a : ℝ := shannonAmplitude j
  let m := shannonCountExponent theta j
  let P := shannonPrefactor theta j alpha
  have hd := shannonScale_pos n
  have hP : 0 ≤ P := (shannonPrefactor_pos theta j alpha).le
  have ha : 0 ≤ Real.rpow (shannonScale n) (a * alpha) :=
    Real.rpow_nonneg hd.le _
  rw [shannonContribution_factorization]
  change (shannonCount theta n j : ℝ) * P *
      Real.rpow (shannonScale n) (a * alpha) ≤
    2 * (P * Real.rpow (shannonScale n) (m + a * alpha))
  simp only [Real.rpow_eq_pow] at *
  rw [Real.rpow_add hd]
  have hc := shannonCount_le_two_mul_rpow theta n j
  change (shannonCount theta n j : ℝ) ≤
    2 * Real.rpow (shannonScale n) m at hc
  have hmul := mul_le_mul_of_nonneg_right hc (mul_nonneg hP ha)
  calc
    (shannonCount theta n j : ℝ) * P *
        Real.rpow (shannonScale n) (a * alpha) =
      (shannonCount theta n j : ℝ) *
        (P * Real.rpow (shannonScale n) (a * alpha)) := by ring
    _ ≤ (2 * Real.rpow (shannonScale n) m) *
        (P * Real.rpow (shannonScale n) (a * alpha)) := hmul
    _ = 2 * (P * (Real.rpow (shannonScale n) m *
        Real.rpow (shannonScale n) (a * alpha))) := by ring

/-- Compact order sets uniformly bound all scale-free prefactor ratios. -/
theorem exists_shannonPrefactor_ratio_bound (theta : ShannonData)
    (I : Set ℝ) (hI : IsCompact I) (_hI0 : I.Nonempty) (k : Fin 3) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ alpha ∈ I, ∀ j : Fin 3,
      shannonPrefactor theta j alpha ≤ M * shannonPrefactor theta k alpha := by
  classical
  have hcont (j : Fin 3) : Continuous
      (fun alpha ↦ shannonPrefactor theta j alpha /
        shannonPrefactor theta k alpha) :=
    (continuous_shannonPrefactor theta j).div
      (continuous_shannonPrefactor theta k)
      (fun alpha ↦ (shannonPrefactor_pos theta k alpha).ne')
  have hb : ∀ j : Fin 3, ∃ C : ℝ, ∀ alpha ∈ I,
      |shannonPrefactor theta j alpha /
        shannonPrefactor theta k alpha| ≤ C := by
    intro j
    simpa only [Real.norm_eq_abs] using
      hI.exists_bound_of_continuousOn (hcont j).continuousOn
  choose C hC using hb
  let M : ℝ := ∑ j : Fin 3, |C j|
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _hj ↦ abs_nonneg (C j)
  refine ⟨M, hM, ?_⟩
  intro alpha h_alpha j
  have hratioNonneg : 0 ≤ shannonPrefactor theta j alpha /
      shannonPrefactor theta k alpha :=
    (div_pos (shannonPrefactor_pos theta j alpha)
      (shannonPrefactor_pos theta k alpha)).le
  have hjM : |C j| ≤ M :=
    Finset.single_le_sum (fun l _hl ↦ abs_nonneg (C l))
      (Finset.mem_univ j)
  have hratioM : shannonPrefactor theta j alpha /
      shannonPrefactor theta k alpha ≤ M := by
    calc
      shannonPrefactor theta j alpha /
          shannonPrefactor theta k alpha =
        |shannonPrefactor theta j alpha /
          shannonPrefactor theta k alpha| :=
            (abs_of_nonneg hratioNonneg).symm
      _ ≤ C j := hC j alpha h_alpha
      _ ≤ |C j| := le_abs_self (C j)
      _ ≤ M := hjM
  rw [div_le_iff₀ (shannonPrefactor_pos theta k alpha)] at hratioM
  exact hratioM

/-- An affine exponent gap and a prefactor-ratio bound suppress a competing
Shannon contribution. -/
theorem shannonContribution_le_decay_mul (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (k j : Fin 3) (alpha eta M : ℝ) (hM : 0 ≤ M)
    (hpref : shannonPrefactor theta j alpha ≤
      M * shannonPrefactor theta k alpha)
    (hgap : eta ≤ shannonExponent theta k alpha -
      shannonExponent theta j alpha) :
    shannonContribution theta n z j alpha ≤
      (2 * M * Real.rpow (shannonScale n) (-eta)) *
        shannonContribution theta n z k alpha := by
  let d := shannonScale n
  let Pj := shannonPrefactor theta j alpha
  let Pk := shannonPrefactor theta k alpha
  let ej := shannonExponent theta j alpha
  let ek := shannonExponent theta k alpha
  have hd : 0 < d := shannonScale_pos n
  have hd1 : 1 ≤ d := (one_lt_shannonScale n).le
  have hPj : 0 ≤ Pj := (shannonPrefactor_pos theta j alpha).le
  have hPk : 0 ≤ Pk := (shannonPrefactor_pos theta k alpha).le
  have hjpow : 0 ≤ Real.rpow d ej := Real.rpow_nonneg hd.le _
  have hkpow : 0 ≤ Real.rpow d ek := Real.rpow_nonneg hd.le _
  have hnegpow : 0 ≤ Real.rpow d (-eta) := Real.rpow_nonneg hd.le _
  have hexp : ej ≤ ek - eta := by
    dsimp only [ej, ek]
    linarith
  have hpow : Real.rpow d ej ≤ Real.rpow d (ek - eta) :=
    Real.rpow_le_rpow_of_exponent_le hd1 hexp
  have hpref' : Pj ≤ M * Pk := by simpa only [Pj, Pk] using hpref
  calc
    shannonContribution theta n z j alpha ≤
        2 * (Pj * Real.rpow d ej) := by
      simpa only [Pj, ej, d] using
        shannonContribution_le_two_mul_ideal theta n z j alpha
    _ ≤ 2 * ((M * Pk) * Real.rpow d (ek - eta)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul hpref' hpow hjpow (mul_nonneg hM hPk)
    _ = (2 * M * Real.rpow d (-eta)) * (Pk * Real.rpow d ek) := by
      simp only [Real.rpow_eq_pow] at *
      rw [show ek - eta = ek + (-eta) by ring, Real.rpow_add hd]
      ring
    _ ≤ (2 * M * Real.rpow d (-eta)) *
        shannonContribution theta n z k alpha := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (mul_nonneg (by norm_num) hM) hnegpow)
      simpa only [Pk, ek, d] using
        shannonIdeal_le_contribution theta n z k alpha

theorem shannonEscort_le_decay (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (k j : Fin 3) (alpha eta M : ℝ) (hM : 0 ≤ M)
    (hpref : shannonPrefactor theta j alpha ≤
      M * shannonPrefactor theta k alpha)
    (hgap : eta ≤ shannonExponent theta k alpha -
      shannonExponent theta j alpha) :
    shannonEscort theta n z j alpha ≤
      2 * M * Real.rpow (shannonScale n) (-eta) := by
  have hkpos := shannonContribution_pos theta n z k alpha
  have hjnonneg := (shannonContribution_pos theta n z j alpha).le
  have hsum : shannonContribution theta n z k alpha ≤
      ∑ l : Fin 3, shannonContribution theta n z l alpha :=
    Finset.single_le_sum
      (fun l _hl ↦ (shannonContribution_pos theta n z l alpha).le)
      (Finset.mem_univ k)
  calc
    shannonEscort theta n z j alpha =
        shannonContribution theta n z j alpha /
          (∑ l : Fin 3, shannonContribution theta n z l alpha) := rfl
    _ ≤ shannonContribution theta n z j alpha /
        shannonContribution theta n z k alpha :=
      div_le_div_of_nonneg_left hjnonneg hkpos hsum
    _ ≤ 2 * M * Real.rpow (shannonScale n) (-eta) := by
      rw [div_le_iff₀ hkpos]
      exact shannonContribution_le_decay_mul theta n z k j alpha eta M
        hM hpref hgap

/-- Uniform outside-mass bound from a compact prefactor bound and a common
affine exponent gap. -/
theorem shannonDominantOutsideMass (theta : ShannonData) (I : Set ℝ)
    (k : Fin 3) (eta M : ℝ) (hM : 0 ≤ M)
    (hpref : ∀ alpha ∈ I, ∀ j : Fin 3,
      shannonPrefactor theta j alpha ≤
        M * shannonPrefactor theta k alpha)
    (hgap : ∀ alpha ∈ I, ∀ j : Fin 3, j ≠ k →
      eta ≤ shannonExponent theta k alpha -
        shannonExponent theta j alpha) :
    ∀ (n : ℕ) (z : ℝ × ℝ) (alpha : ℝ), alpha ∈ I →
      ∑ j ∈ Finset.univ.erase k, shannonEscort theta n z j alpha ≤
        (6 * M) * Real.rpow (shannonScale n) (-eta) := by
  intro n z alpha h_alpha
  have hdecay : 0 ≤ 2 * M * Real.rpow (shannonScale n) (-eta) :=
    mul_nonneg (mul_nonneg (by norm_num) hM)
      (Real.rpow_nonneg (shannonScale_pos n).le _)
  calc
    ∑ j ∈ Finset.univ.erase k, shannonEscort theta n z j alpha ≤
        ∑ _j ∈ Finset.univ.erase k,
          2 * M * Real.rpow (shannonScale n) (-eta) := by
      apply Finset.sum_le_sum
      intro j hj
      exact shannonEscort_le_decay theta n z k j alpha eta M hM
        (hpref alpha h_alpha j)
        (hgap alpha h_alpha j (Finset.ne_of_mem_erase hj))
    _ = ((Finset.univ.erase k).card : ℝ) *
          (2 * M * Real.rpow (shannonScale n) (-eta)) := by simp
    _ ≤ (Fintype.card (Fin 3) : ℝ) *
          (2 * M * Real.rpow (shannonScale n) (-eta)) := by
      apply mul_le_mul_of_nonneg_right _ hdecay
      exact_mod_cast Finset.card_le_card (Finset.erase_subset k Finset.univ)
    _ = (6 * M) * Real.rpow (shannonScale n) (-eta) := by
      simp only [Fintype.card_fin, Nat.cast_ofNat]
      ring

/-- Compact perturbation sets give one velocity bound, uniform in the scale
and in all three Shannon blocks. -/
theorem exists_uniform_shannonVelocity_bound (theta : ShannonData)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ n : ℕ, ∀ z ∈ K, ∀ j : Fin 3,
      |shannonBlockVelocity theta n z j| ≤ U := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ × ℝ)
  let B := max R 0
  let ltwo := Real.log (2 : ℝ)
  let U := B / (theta.q * ltwo) + B / (theta.p * ltwo) + B
  have hB : 0 ≤ B := le_max_right _ _
  have htwo : 0 < ltwo := log_two_pos
  have hqden : 0 ≤ theta.q * ltwo :=
    mul_nonneg theta.q_pos.le htwo.le
  have hpden : 0 ≤ theta.p * ltwo :=
    mul_nonneg theta.p_pos.le htwo.le
  have hqterm : 0 ≤ B / (theta.q * ltwo) := div_nonneg hB hqden
  have hpterm : 0 ≤ B / (theta.p * ltwo) := div_nonneg hB hpden
  have hU : 0 ≤ U := by
    dsimp only [U]
    exact add_nonneg (add_nonneg hqterm hpterm) hB
  refine ⟨U, hU, ?_⟩
  intro n z hz j
  have hzBall := hR hz
  have hznorm : ‖z‖ ≤ R := by
    simpa [dist_zero_right] using hzBall
  have hfirst : |z.1| ≤ B := by
    calc
      |z.1| = ‖z.1‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖z‖ := norm_fst_le z
      _ ≤ R := hznorm
      _ ≤ B := le_max_left _ _
  have hsecond : |z.2| ≤ B := by
    calc
      |z.2| = ‖z.2‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖z‖ := norm_snd_le z
      _ ≤ R := hznorm
      _ ≤ B := le_max_left _ _
  have htwoL : ltwo ≤ shannonLogScale n := log_two_le_shannonLogScale n
  fin_cases j
  · change |z.1 / (theta.q * shannonLogScale n)| ≤ U
    rw [abs_div,
      abs_of_pos (mul_pos theta.q_pos (shannonLogScale_pos n))]
    calc
      |z.1| / (theta.q * shannonLogScale n) ≤
          B / (theta.q * shannonLogScale n) :=
        div_le_div_of_nonneg_right hfirst
          (mul_nonneg theta.q_pos.le (shannonLogScale_pos n).le)
      _ ≤ B / (theta.q * ltwo) := by
        exact div_le_div_of_nonneg_left hB (mul_pos theta.q_pos htwo)
          (mul_le_mul_of_nonneg_left htwoL theta.q_pos.le)
      _ ≤ U := by
        dsimp only [U]
        linarith
  · change |-z.1 / (theta.p * shannonLogScale n)| ≤ U
    rw [abs_div, abs_neg,
      abs_of_pos (mul_pos theta.p_pos (shannonLogScale_pos n))]
    calc
      |z.1| / (theta.p * shannonLogScale n) ≤
          B / (theta.p * shannonLogScale n) :=
        div_le_div_of_nonneg_right hfirst
          (mul_nonneg theta.p_pos.le (shannonLogScale_pos n).le)
      _ ≤ B / (theta.p * ltwo) := by
        exact div_le_div_of_nonneg_left hB (mul_pos theta.p_pos htwo)
          (mul_le_mul_of_nonneg_left htwoL theta.p_pos.le)
      _ ≤ U := by
        dsimp only [U]
        linarith
  · change |z.2| ≤ U
    exact hsecond.trans (by
      dsimp only [U]
      linarith)

/-- Full Shannon analogue of the generic dominant-block package.  The
velocity bound is supplied separately so that compactness of the perturbation
set can be used once by the caller. -/
theorem shannonDominantEstimates (theta : ShannonData) (I : Set ℝ)
    (k : Fin 3) (eta M U : ℝ) (hM : 0 ≤ M) (hU : 0 ≤ U)
    (hpref : ∀ alpha ∈ I, ∀ j : Fin 3,
      shannonPrefactor theta j alpha ≤
        M * shannonPrefactor theta k alpha)
    (hgap : ∀ alpha ∈ I, ∀ j : Fin 3, j ≠ k →
      eta ≤ shannonExponent theta k alpha -
        shannonExponent theta j alpha) :
    ∃ C_I C_K : ℝ, 0 ≤ C_I ∧ 0 ≤ C_K ∧
      ∀ (n : ℕ) (z : ℝ × ℝ),
        (∀ j, |shannonBlockVelocity theta n z j| ≤ U) →
        ∀ alpha ∈ I,
          (∑ j ∈ Finset.univ.erase k,
              shannonEscort theta n z j alpha ≤
            C_I * Real.rpow (shannonScale n) (-eta)) ∧
          (|shannonMean theta n z alpha -
                shannonBlockVelocity theta n z k| +
              |shannonSecond theta n z alpha -
                shannonBlockVelocity theta n z k ^ 2| +
              shannonVar theta n z alpha ≤
            C_K * Real.rpow (shannonScale n) (-eta)) ∧
          (|deriv (fun s ↦ shannonMean theta n z s) alpha| +
              |deriv (fun s ↦ shannonSecond theta n z s) alpha| ≤
            C_K * shannonLogScale n *
              Real.rpow (shannonScale n) (-eta)) := by
  let C_I : ℝ := 6 * M
  let A : ℝ := 2 * U + 2 * U ^ 2 + 4 * U ^ 2
  let D : ℝ := 36 * shannonLogBaseCoeff theta
  let C_m : ℝ := A * C_I
  let C_d : ℝ := (U + U ^ 2) * D * C_I
  let C_K : ℝ := C_m + C_d
  have hCI : 0 ≤ C_I := mul_nonneg (by norm_num) hM
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hD : 0 ≤ D :=
    mul_nonneg (by norm_num) (shannonLogBaseCoeff_nonneg theta)
  have hCm : 0 ≤ C_m := mul_nonneg hA hCI
  have hCd : 0 ≤ C_d := by
    exact mul_nonneg (mul_nonneg (add_nonneg hU (sq_nonneg U)) hD) hCI
  have hCK : 0 ≤ C_K := add_nonneg hCm hCd
  refine ⟨C_I, C_K, hCI, hCK, ?_⟩
  intro n z hu alpha h_alpha
  let r := Real.rpow (shannonScale n) (-eta)
  let L := shannonLogScale n
  let R := ∑ j ∈ Finset.univ.erase k,
    shannonEscort theta n z j alpha
  have hr : 0 ≤ r := Real.rpow_nonneg (shannonScale_pos n).le _
  have hL : 0 ≤ L := (shannonLogScale_pos n).le
  have hout : R ≤ C_I * r := by
    simpa only [R, C_I, r] using
      shannonDominantOutsideMass theta I k eta M hM hpref hgap
        n z alpha h_alpha
  refine ⟨hout, ?_, ?_⟩
  · have hm := abs_shannonMean_sub_le_outside theta n z alpha k U hu
    have hs := abs_shannonSecond_sub_le_outside theta n z alpha k U hU hu
    have hv := shannonVar_le_outside theta n z alpha k U hU hu
    calc
      |shannonMean theta n z alpha - shannonBlockVelocity theta n z k| +
          |shannonSecond theta n z alpha -
            shannonBlockVelocity theta n z k ^ 2| +
          shannonVar theta n z alpha ≤
        (2 * U) * R + (2 * U ^ 2) * R + (4 * U ^ 2) * R :=
          add_le_add (add_le_add hm hs) hv
      _ = A * R := by dsimp only [A]; ring
      _ ≤ A * (C_I * r) := mul_le_mul_of_nonneg_left hout hA
      _ = C_m * r := by dsimp only [C_m]; ring
      _ ≤ C_K * r := by
        exact mul_le_mul_of_nonneg_right
          (by dsimp only [C_K]; exact le_add_of_nonneg_right hCd) hr
  · have hsum := sum_abs_deriv_shannonEscort_order_le_outside
      theta n z k alpha
    have hdiam := shannonLogDiameter_le theta n z
    have hmean := abs_deriv_shannonMean_order_le theta n z U alpha hU hu
    have hsecond := abs_deriv_shannonSecond_order_le theta n z U alpha hU hu
    let S := ∑ j : Fin 3,
      |deriv (fun s ↦ shannonEscort theta n z j s) alpha|
    have hS : S ≤ D * L * R := by
      calc
        S ≤ (2 * shannonLogDiameter theta n z) * R := by
          simpa only [S, R] using hsum
        _ ≤ (2 * ((18 * shannonLogBaseCoeff theta) * L)) * R := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdiam (by norm_num))
            (Finset.sum_nonneg fun j _hj ↦
              shannonEscort_nonneg theta n z j alpha)
        _ = D * L * R := by dsimp only [D, L]; ring
    calc
      |deriv (fun s ↦ shannonMean theta n z s) alpha| +
          |deriv (fun s ↦ shannonSecond theta n z s) alpha| ≤
        U * S + U ^ 2 * S := add_le_add hmean hsecond
      _ = (U + U ^ 2) * S := by ring
      _ ≤ (U + U ^ 2) * (D * L * R) :=
        mul_le_mul_of_nonneg_left hS (add_nonneg hU (sq_nonneg U))
      _ ≤ (U + U ^ 2) * (D * L * (C_I * r)) := by
        apply mul_le_mul_of_nonneg_left _ (add_nonneg hU (sq_nonneg U))
        exact mul_le_mul_of_nonneg_left hout (mul_nonneg hD hL)
      _ = C_d * L * r := by dsimp only [C_d]; ring
      _ ≤ C_K * L * r := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (by dsimp only [C_K]; exact le_add_of_nonneg_left hCm) hL) hr

end ConditionalEntropy
