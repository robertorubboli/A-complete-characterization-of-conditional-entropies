import ConditionalEntropy.ShannonDominance

/-!
# Dedicated Shannon escort estimates

This module instantiates the affine-exponent calculus for the three regions
separated by the crossings at orders `1` and `theta.c`.
-/

noncomputable section

open Filter Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

/-- The third Shannon block is uniformly negligible on a sufficiently small
fixed neighbourhood of order one, including its order derivative. -/
theorem shannonDedicatedEscortNearOne (theta : ShannonData)
    (K : Set (ℝ × ℝ)) (_hK : IsCompact K) (_hK0 : K.Nonempty) :
    ∀ delta : ℝ, 0 < delta →
      delta < min (1 / 2 : ℝ) ((theta.c - 1) / 4) →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (n : ℕ) (z : ℝ × ℝ), z ∈ K →
          ∀ alpha ∈ Icc (1 - delta) (1 + delta),
            shannonEscort theta n z 2 alpha ≤
                C * Real.rpow (shannonScale n) (-(theta.c - 1) / 2) ∧
              |deriv (fun s ↦ shannonEscort theta n z 2 s) alpha| ≤
                C * shannonLogScale n *
                  Real.rpow (shannonScale n) (-(theta.c - 1) / 2) := by
  intro delta hdelta0 hdelta
  let I : Set ℝ := Icc (1 - delta) (1 + delta)
  have hI : IsCompact I := isCompact_Icc
  have hI0 : I.Nonempty := nonempty_Icc.mpr (by linarith)
  obtain ⟨M, hM, hpref⟩ :=
    exists_shannonPrefactor_ratio_bound theta I hI hI0 0
  let eta : ℝ := (theta.c - 1) / 2
  let C₀ : ℝ := 2 * M
  let D : ℝ := 18 * shannonLogBaseCoeff theta
  let C₁ : ℝ := C₀ * D
  let C : ℝ := C₀ + C₁
  have heta : 0 < eta := by
    dsimp only [eta]
    linarith [theta.c_gt_one]
  have hC₀ : 0 ≤ C₀ := mul_nonneg (by norm_num) hM
  have hD : 0 ≤ D :=
    mul_nonneg (by norm_num) (shannonLogBaseCoeff_nonneg theta)
  have hC₁ : 0 ≤ C₁ := mul_nonneg hC₀ hD
  have hC : 0 ≤ C := add_nonneg hC₀ hC₁
  have hC₀C : C₀ ≤ C := by
    change C₀ ≤ C₀ + C₁
    exact le_add_of_nonneg_right hC₁
  have hC₁C : C₁ ≤ C := by
    change C₁ ≤ C₀ + C₁
    exact le_add_of_nonneg_left hC₀
  refine ⟨C, hC, ?_⟩
  intro n z _hz alpha h_alpha
  have hdeltaC : delta < (theta.c - 1) / 4 :=
    (lt_min_iff.mp hdelta).2
  have hgap : eta ≤ shannonExponent theta 0 alpha -
      shannonExponent theta 2 alpha := by
    rw [shannonExponent_zero, shannonExponent_two]
    dsimp only [eta, I] at h_alpha ⊢
    linarith [h_alpha.2]
  have hesc0 := shannonEscort_le_decay theta n z 0 2 alpha eta M hM
    (hpref alpha h_alpha 2) hgap
  have hesc : shannonEscort theta n z 2 alpha ≤
      C₀ * Real.rpow (shannonScale n) (-eta) := by
    simpa only [C₀] using hesc0
  let r := Real.rpow (shannonScale n) (-eta)
  let L := shannonLogScale n
  have hr : 0 ≤ r := Real.rpow_nonneg (shannonScale_pos n).le _
  have hL : 0 ≤ L := (shannonLogScale_pos n).le
  have hdiam := shannonLogDiameter_le theta n z
  have hcenter := abs_shannonLogBase_sub_escortMean_le theta n z 2 alpha
  have hderiv : |deriv (fun s ↦ shannonEscort theta n z 2 s) alpha| ≤
      C₁ * L * r := by
    rw [abs_deriv_shannonEscort_order]
    calc
      shannonEscort theta n z 2 alpha *
          |shannonLogBase theta n z 2 -
            shannonEscortLogMean theta n z alpha| ≤
        (C₀ * r) * shannonLogDiameter theta n z :=
          mul_le_mul hesc hcenter (abs_nonneg _)
            (mul_nonneg hC₀ hr)
      _ ≤ (C₀ * r) * (D * L) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC₀ hr)
        simpa only [D, L] using hdiam
      _ = C₁ * L * r := by dsimp only [C₁]; ring
  constructor
  · have h := hesc.trans (mul_le_mul_of_nonneg_right
      hC₀C hr)
    simpa only [eta, neg_div] using h
  · have h := hderiv.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        hC₁C hL) hr)
    simpa only [L, r, eta, neg_div] using h

/-- A compact order interval avoiding both crossings admits a single
dominant Shannon block and a strictly positive affine exponent gap. -/
theorem exists_shannonDominantGap (theta : ShannonData) (I : Set ℝ)
    (hI : IsCompact I) (hI0 : I.Nonempty) (hconn : OrdConnected I)
    (_hIpos : I ⊆ Ici (0 : ℝ))
    (havoid : I ∩ {1, theta.c} = ∅) :
    ∃ k : Fin 3, ∃ eta : ℝ, 0 < eta ∧
      ∀ alpha ∈ I, ∀ j : Fin 3, j ≠ k →
        eta ≤ shannonExponent theta k alpha -
          shannonExponent theta j alpha := by
  have hnot1 : (1 : ℝ) ∉ I := by
    intro h1
    have hmem : (1 : ℝ) ∈ I ∩ {1, theta.c} := ⟨h1, by simp⟩
    rw [havoid] at hmem
    exact hmem
  have hnotc : theta.c ∉ I := by
    intro hc
    have hmem : theta.c ∈ I ∩ {1, theta.c} := ⟨hc, by simp⟩
    rw [havoid] at hmem
    exact hmem
  obtain ⟨x, hx⟩ := hI0
  have hx1 : x < 1 ∨ 1 < x := lt_or_gt_of_ne (by
    intro h
    exact hnot1 (h ▸ hx))
  rcases hx1 with hxlow | hxhigh
  · have hbelow : I ⊆ Iio (1 : ℝ) := by
      intro alpha h_alpha
      by_contra hnot
      have hle : (1 : ℝ) ≤ alpha := le_of_not_gt hnot
      have honeMem : (1 : ℝ) ∈ Icc x alpha := ⟨hxlow.le, hle⟩
      exact hnot1 (hconn.out hx h_alpha honeMem)
    obtain ⟨a, haI, haMax⟩ :=
      hI.exists_isMaxOn ⟨x, hx⟩ continuous_id.continuousOn
    have ha_lt : a < 1 := hbelow haI
    let eta : ℝ := 1 - a
    have heta : 0 < eta := sub_pos.mpr ha_lt
    refine ⟨0, eta, heta, ?_⟩
    intro alpha h_alpha j hj
    have halpha : alpha ≤ a := (isMaxOn_iff.mp haMax) alpha h_alpha
    rcases j with ⟨j, hjlt⟩
    interval_cases j
    · exact (hj rfl).elim
    · simp [shannonExponent, shannonCountExponent, shannonAmplitude]
      dsimp only [eta]
      linarith
    · simp [shannonExponent, shannonCountExponent, shannonAmplitude]
      dsimp only [eta]
      linarith [theta.c_gt_one]
  · have hxc : x < theta.c ∨ theta.c < x := lt_or_gt_of_ne (by
      intro h
      exact hnotc (h ▸ hx))
    rcases hxc with hxmiddle | hxabove
    · have hmiddle : I ⊆ Ioo (1 : ℝ) theta.c := by
        intro alpha h_alpha
        constructor
        · by_contra hnot
          have hle : alpha ≤ (1 : ℝ) := le_of_not_gt hnot
          have honeMem : (1 : ℝ) ∈ Icc alpha x := ⟨hle, hxhigh.le⟩
          exact hnot1 (hconn.out h_alpha hx honeMem)
        · by_contra hnot
          have hle : theta.c ≤ alpha := le_of_not_gt hnot
          have hcMem : theta.c ∈ Icc x alpha := ⟨hxmiddle.le, hle⟩
          exact hnotc (hconn.out hx h_alpha hcMem)
      obtain ⟨a, haI, haMin⟩ :=
        hI.exists_isMinOn ⟨x, hx⟩ continuous_id.continuousOn
      obtain ⟨b, hbI, hbMax⟩ :=
        hI.exists_isMaxOn ⟨x, hx⟩ continuous_id.continuousOn
      have ha_gt : 1 < a := (hmiddle haI).1
      have hb_lt : b < theta.c := (hmiddle hbI).2
      let eta : ℝ := min (a - 1) (theta.c - b)
      have heta : 0 < eta := lt_min (sub_pos.mpr ha_gt) (sub_pos.mpr hb_lt)
      refine ⟨1, eta, heta, ?_⟩
      intro alpha h_alpha j hj
      have halphaMin : a ≤ alpha := (isMinOn_iff.mp haMin) alpha h_alpha
      have halphaMax : alpha ≤ b := (isMaxOn_iff.mp hbMax) alpha h_alpha
      rcases j with ⟨j, hjlt⟩
      interval_cases j
      · simp only [Fin.isValue, shannonExponent_one, Fin.zero_eta,
          shannonExponent_zero, ge_iff_le]
        dsimp only [eta]
        exact (min_le_left (a - 1) (theta.c - b)).trans (by linarith)
      · exact (hj rfl).elim
      · simp only [Fin.isValue, shannonExponent_one, Fin.reduceFinMk,
          shannonExponent_two, ge_iff_le]
        dsimp only [eta]
        exact (min_le_right (a - 1) (theta.c - b)).trans (by linarith)
    · have habove : I ⊆ Ioi theta.c := by
        intro alpha h_alpha
        by_contra hnot
        have hle : alpha ≤ theta.c := le_of_not_gt hnot
        have hcMem : theta.c ∈ Icc alpha x := ⟨hle, hxabove.le⟩
        exact hnotc (hconn.out h_alpha hx hcMem)
      obtain ⟨a, haI, haMin⟩ :=
        hI.exists_isMinOn ⟨x, hx⟩ continuous_id.continuousOn
      have ha_gt : theta.c < a := habove haI
      let eta : ℝ := a - theta.c
      have heta : 0 < eta := sub_pos.mpr ha_gt
      refine ⟨2, eta, heta, ?_⟩
      intro alpha h_alpha j hj
      have halpha : a ≤ alpha := (isMinOn_iff.mp haMin) alpha h_alpha
      rcases j with ⟨j, hjlt⟩
      interval_cases j
      · simp [shannonExponent, shannonCountExponent, shannonAmplitude]
        dsimp only [eta]
        linarith [theta.c_gt_one]
      · simp [shannonExponent, shannonCountExponent, shannonAmplitude]
        dsimp only [eta]
        linarith
      · exact (hj rfl).elim

/-- Compact-region clause of the dedicated Shannon escort theorem. -/
theorem shannonDedicatedEscortCompact (theta : ShannonData)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) (_hK0 : K.Nonempty) :
    ∀ I : Set ℝ, IsCompact I → I.Nonempty → OrdConnected I →
      I ⊆ Ici (0 : ℝ) → I ∩ {1, theta.c} = ∅ →
      ∃ (k : Fin 3) (eta C_I C_K : ℝ),
        0 < eta ∧ 0 ≤ C_I ∧ 0 ≤ C_K ∧
          ∀ (n : ℕ) (z : ℝ × ℝ), z ∈ K → ∀ alpha ∈ I,
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
  intro I hI hI0 hconn hIpos havoid
  obtain ⟨k, eta, heta, hgap⟩ :=
    exists_shannonDominantGap theta I hI hI0 hconn hIpos havoid
  obtain ⟨M, hM, hpref⟩ :=
    exists_shannonPrefactor_ratio_bound theta I hI hI0 k
  obtain ⟨U, hU, hu⟩ := exists_uniform_shannonVelocity_bound theta K hK
  obtain ⟨C_I, C_K, hCI, hCK, hest⟩ :=
    shannonDominantEstimates theta I k eta M U hM hU hpref hgap
  refine ⟨k, eta, C_I, C_K, heta, hCI, hCK, ?_⟩
  intro n z hz alpha h_alpha
  exact hest n z (hu n z hz) alpha h_alpha

/-- Large-order tail and endpoint clause of the dedicated Shannon escort
theorem. -/
theorem shannonDedicatedEscortTail (theta : ShannonData)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) (_hK0 : K.Nonempty) :
    ∃ A gamma C : ℝ, theta.c < A ∧ 0 < gamma ∧ 0 ≤ C ∧
      ∀ (n : ℕ) (z : ℝ × ℝ), z ∈ K → ∀ alpha : ℝ, A ≤ alpha →
        shannonEscort theta n z 0 alpha +
            shannonEscort theta n z 1 alpha ≤
          C * Real.rpow (shannonScale n) (-gamma * alpha) ∧
        alpha * (shannonEscort theta n z 0 alpha +
            shannonEscort theta n z 1 alpha) ≤ C ∧
        |shannonKOne theta n z (finiteParam alpha)| ≤ C ∧
        |shannonKTwo theta n z (finiteParam alpha)| ≤ C ∧
        |shannonKOne theta n z ⊤| ≤ C ∧
        |shannonKTwo theta n z ⊤| ≤ C := by
  obtain ⟨U, hU, hu⟩ := exists_uniform_shannonVelocity_bound theta K hK
  let A : ℝ := 2 * theta.c
  let gamma : ℝ := 1 / 2
  let N : ℝ := 4
  let T : ℝ := N * (gamma * Real.log 2)⁻¹
  let F₁ : ℝ := 4 * U
  let F₂ : ℝ := 4 * U ^ 2 * T + 4 * U ^ 2
  let E₁ : ℝ := 2 * U
  let E₂ : ℝ := 2 * U ^ 2
  let C : ℝ := N + T + F₁ + F₂ + E₁ + E₂
  have hA : theta.c < A := by
    dsimp only [A]
    linarith [theta.c_gt_one]
  have hA2 : (2 : ℝ) ≤ A := by
    dsimp only [A]
    linarith [theta.c_gt_one]
  have hgamma : 0 < gamma := by norm_num [gamma]
  have hN : 0 ≤ N := by norm_num [N]
  have hT : 0 ≤ T := by
    dsimp only [T]
    positivity
  have hF₁ : 0 ≤ F₁ := by dsimp only [F₁]; positivity
  have hF₂ : 0 ≤ F₂ := by dsimp only [F₂]; positivity
  have hE₁ : 0 ≤ E₁ := by dsimp only [E₁]; positivity
  have hE₂ : 0 ≤ E₂ := by dsimp only [E₂]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hNC : N ≤ C := by dsimp only [C]; linarith
  have hTC : T ≤ C := by dsimp only [C]; linarith
  have hF₁C : F₁ ≤ C := by dsimp only [C]; linarith
  have hF₂C : F₂ ≤ C := by dsimp only [C]; linarith
  have hE₁C : E₁ ≤ C := by dsimp only [C]; linarith
  have hE₂C : E₂ ≤ C := by dsimp only [C]; linarith
  refine ⟨A, gamma, C, hA, hgamma, hC, ?_⟩
  intro n z hz alpha h_alpha
  have htwo : (2 : ℝ) ≤ alpha := hA2.trans h_alpha
  have halpha : 0 ≤ alpha := by linarith
  have hpos : 0 < alpha := by linarith
  have hone : alpha ≠ 1 := by linarith
  have hpref0 : shannonPrefactor theta 0 alpha ≤
      1 * shannonPrefactor theta 2 alpha := by
    simp only [shannonPrefactor_zero, shannonPrefactor_two, mul_one]
    exact Real.rpow_le_one theta.q_pos.le theta.q_lt_one.le halpha
  have hpref1 : shannonPrefactor theta 1 alpha ≤
      1 * shannonPrefactor theta 2 alpha := by
    simp only [shannonPrefactor_one, shannonPrefactor_two, mul_one]
    exact Real.rpow_le_one theta.p_pos.le theta.p_lt_one.le halpha
  have hgap0 : gamma * alpha ≤ shannonExponent theta 2 alpha -
      shannonExponent theta 0 alpha := by
    rw [shannonExponent_two, shannonExponent_zero]
    dsimp only [gamma, A] at h_alpha ⊢
    nlinarith [theta.c_gt_one]
  have hgap1 : gamma * alpha ≤ shannonExponent theta 2 alpha -
      shannonExponent theta 1 alpha := by
    rw [shannonExponent_two, shannonExponent_one]
    dsimp only [gamma, A] at h_alpha ⊢
    nlinarith
  have hesc0 := shannonEscort_le_decay theta n z 2 0 alpha
    (gamma * alpha) 1 (by norm_num) hpref0 hgap0
  have hesc1 := shannonEscort_le_decay theta n z 2 1 alpha
    (gamma * alpha) 1 (by norm_num) hpref1 hgap1
  let r := Real.rpow (shannonScale n) (-gamma * alpha)
  have hr : 0 ≤ r := Real.rpow_nonneg (shannonScale_pos n).le _
  have houtN : shannonEscort theta n z 0 alpha +
      shannonEscort theta n z 1 alpha ≤ N * r := by
    calc
      shannonEscort theta n z 0 alpha +
          shannonEscort theta n z 1 alpha ≤
        (2 * 1 * r) + (2 * 1 * r) := by
          exact add_le_add (by simpa only [r, neg_mul] using hesc0)
            (by simpa only [r, neg_mul] using hesc1)
      _ = N * r := by dsimp only [N]; ring
  have houtC : shannonEscort theta n z 0 alpha +
      shannonEscort theta n z 1 alpha ≤ C * r :=
    houtN.trans (mul_le_mul_of_nonneg_right hNC hr)
  have hweightedN : alpha * (shannonEscort theta n z 0 alpha +
      shannonEscort theta n z 1 alpha) ≤ T := by
    calc
      alpha * (shannonEscort theta n z 0 alpha +
          shannonEscort theta n z 1 alpha) ≤ alpha * (N * r) :=
        mul_le_mul_of_nonneg_left houtN halpha
      _ = N * (alpha * r) := by ring
      _ ≤ N * (gamma * Real.log 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ hN
        simpa only [r, shannonScale] using
          alpha_mul_rpow_blockScale_le_inv n hgamma halpha
      _ = T := by rfl
  have hweightedC : alpha * (shannonEscort theta n z 0 alpha +
      shannonEscort theta n z 1 alpha) ≤ C := hweightedN.trans hTC
  have hvel := hu n z hz
  have hmeanAlpha := abs_shannonMean_le theta n z alpha U hvel
  have hmeanOne := abs_shannonMean_le theta n z 1 U hvel
  have hmeanDiff : |shannonMean theta n z alpha -
      shannonMean theta n z 1| ≤ 2 * U := by
    calc
      |shannonMean theta n z alpha - shannonMean theta n z 1| ≤
          |shannonMean theta n z alpha| + |shannonMean theta n z 1| :=
        abs_sub _ _
      _ ≤ U + U := add_le_add hmeanAlpha hmeanOne
      _ = 2 * U := by ring
  have hfirst : |shannonKOne theta n z (finiteParam alpha)| ≤ F₁ := by
    rw [shannonKOne_finite theta n z hpos hone, abs_mul]
    calc
      |singularWeight (finiteParam alpha)| *
          |shannonMean theta n z alpha - shannonMean theta n z 1| ≤
        2 * (2 * U) :=
          mul_le_mul (abs_singularWeight_finite_le_two htwo) hmeanDiff
            (abs_nonneg _) (by positivity)
      _ = F₁ := by dsimp only [F₁]; ring
  have hR : (∑ j ∈ Finset.univ.erase (2 : Fin 3),
      shannonEscort theta n z j alpha) =
      shannonEscort theta n z 0 alpha +
        shannonEscort theta n z 1 alpha :=
    sum_shannonEscort_erase_two theta n z alpha
  have hvar := shannonVar_le_outside theta n z alpha 2 U hU hvel
  have hvarTerm : alpha * shannonVar theta n z alpha ≤
      4 * U ^ 2 * T := by
    calc
      alpha * shannonVar theta n z alpha ≤
          alpha * ((4 * U ^ 2) *
            (shannonEscort theta n z 0 alpha +
              shannonEscort theta n z 1 alpha)) := by
        apply mul_le_mul_of_nonneg_left _ halpha
        simpa only [hR] using hvar
      _ = (4 * U ^ 2) *
          (alpha * (shannonEscort theta n z 0 alpha +
            shannonEscort theta n z 1 alpha)) := by ring
      _ ≤ (4 * U ^ 2) * T :=
        mul_le_mul_of_nonneg_left hweightedN (by positivity)
  have hmeanOneSq : shannonMean theta n z 1 ^ 2 ≤ U ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_nonneg hU] using hmeanOne)
  have hmeanAlphaSq : shannonMean theta n z alpha ^ 2 ≤ U ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_nonneg hU] using hmeanAlpha)
  have hsqDiff : |shannonMean theta n z 1 ^ 2 -
      shannonMean theta n z alpha ^ 2| ≤ 2 * U ^ 2 := by
    calc
      |shannonMean theta n z 1 ^ 2 -
          shannonMean theta n z alpha ^ 2| ≤
        |shannonMean theta n z 1 ^ 2| +
          |shannonMean theta n z alpha ^ 2| := abs_sub _ _
      _ = shannonMean theta n z 1 ^ 2 +
          shannonMean theta n z alpha ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
      _ ≤ U ^ 2 + U ^ 2 := add_le_add hmeanOneSq hmeanAlphaSq
      _ = 2 * U ^ 2 := by ring
  have hsingTerm : |singularWeight (finiteParam alpha) *
      (shannonMean theta n z 1 ^ 2 -
        shannonMean theta n z alpha ^ 2)| ≤ 4 * U ^ 2 := by
    rw [abs_mul]
    calc
      |singularWeight (finiteParam alpha)| *
          |shannonMean theta n z 1 ^ 2 -
            shannonMean theta n z alpha ^ 2| ≤
        2 * (2 * U ^ 2) :=
          mul_le_mul (abs_singularWeight_finite_le_two htwo) hsqDiff
            (abs_nonneg _) (by positivity)
      _ = 4 * U ^ 2 := by ring
  have hsecond : |shannonKTwo theta n z (finiteParam alpha)| ≤ F₂ := by
    rw [shannonKTwo_finite theta n z hpos hone]
    calc
      |-alpha * shannonVar theta n z alpha +
          singularWeight (finiteParam alpha) *
            (shannonMean theta n z 1 ^ 2 -
              shannonMean theta n z alpha ^ 2)| ≤
        |-alpha * shannonVar theta n z alpha| +
          |singularWeight (finiteParam alpha) *
            (shannonMean theta n z 1 ^ 2 -
              shannonMean theta n z alpha ^ 2)| := abs_add_le _ _
      _ ≤ 4 * U ^ 2 * T + 4 * U ^ 2 := by
        rw [abs_mul, abs_neg, abs_of_pos hpos,
          abs_of_nonneg (shannonVar_nonneg theta n z alpha)]
        exact add_le_add hvarTerm hsingTerm
      _ = F₂ := rfl
  have htopFirst : |shannonKOne theta n z ⊤| ≤ E₁ := by
    rw [shannonKOne_top]
    calc
      |shannonMean theta n z 1 - z.2| ≤
          |shannonMean theta n z 1| + |z.2| := abs_sub _ _
      _ ≤ U + U := add_le_add hmeanOne (by
        simpa only [shannonBlockVelocity_two] using hvel 2)
      _ = E₁ := by dsimp only [E₁]; ring
  have htopSecond : |shannonKTwo theta n z ⊤| ≤ E₂ := by
    rw [shannonKTwo_top]
    have hzSq : z.2 ^ 2 ≤ U ^ 2 :=
      sq_le_sq.mpr (by simpa only [abs_of_nonneg hU,
        shannonBlockVelocity_two] using hvel 2)
    calc
      |z.2 ^ 2 - shannonMean theta n z 1 ^ 2| ≤
          |z.2 ^ 2| + |shannonMean theta n z 1 ^ 2| := abs_sub _ _
      _ = z.2 ^ 2 + shannonMean theta n z 1 ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
      _ ≤ U ^ 2 + U ^ 2 := add_le_add hzSq hmeanOneSq
      _ = E₂ := by dsimp only [E₂]; ring
  exact ⟨houtC, hweightedC, hfirst.trans hF₁C, hsecond.trans hF₂C,
    htopFirst.trans hE₁C, htopSecond.trans hE₂C⟩

/-- The exact three-clause dedicated Shannon escort interface from the
localization argument. -/
theorem shannonDedicatedEscort (theta : ShannonData) (K : Set (ℝ × ℝ))
    (hK : IsCompact K) (hK0 : K.Nonempty) :
    (∀ delta : ℝ, 0 < delta →
      delta < min (1 / 2 : ℝ) ((theta.c - 1) / 4) →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (n : ℕ) (z : ℝ × ℝ), z ∈ K →
          ∀ alpha ∈ Icc (1 - delta) (1 + delta),
            shannonEscort theta n z 2 alpha ≤
                C * Real.rpow (shannonScale n) (-(theta.c - 1) / 2) ∧
              |deriv (fun s ↦ shannonEscort theta n z 2 s) alpha| ≤
                C * shannonLogScale n *
                  Real.rpow (shannonScale n) (-(theta.c - 1) / 2)) ∧
    (∀ I : Set ℝ, IsCompact I → I.Nonempty → OrdConnected I →
      I ⊆ Ici (0 : ℝ) → I ∩ {1, theta.c} = ∅ →
      ∃ (k : Fin 3) (eta C_I C_K : ℝ),
        0 < eta ∧ 0 ≤ C_I ∧ 0 ≤ C_K ∧
          ∀ (n : ℕ) (z : ℝ × ℝ), z ∈ K → ∀ alpha ∈ I,
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
                Real.rpow (shannonScale n) (-eta))) ∧
    (∃ A gamma C : ℝ, theta.c < A ∧ 0 < gamma ∧ 0 ≤ C ∧
      ∀ (n : ℕ) (z : ℝ × ℝ), z ∈ K → ∀ alpha : ℝ, A ≤ alpha →
        shannonEscort theta n z 0 alpha +
            shannonEscort theta n z 1 alpha ≤
          C * Real.rpow (shannonScale n) (-gamma * alpha) ∧
        alpha * (shannonEscort theta n z 0 alpha +
            shannonEscort theta n z 1 alpha) ≤ C ∧
        |shannonKOne theta n z (finiteParam alpha)| ≤ C ∧
        |shannonKTwo theta n z (finiteParam alpha)| ≤ C ∧
        |shannonKOne theta n z ⊤| ≤ C ∧
        |shannonKTwo theta n z ⊤| ≤ C) := by
  exact ⟨shannonDedicatedEscortNearOne theta K hK hK0,
    shannonDedicatedEscortCompact theta K hK hK0,
    shannonDedicatedEscortTail theta K hK hK0⟩

end ConditionalEntropy
