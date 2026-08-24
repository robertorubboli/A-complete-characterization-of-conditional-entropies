import ConditionalEntropy.FiniteChannels
import ConditionalEntropy.FiniteExtrema
import ConditionalEntropy.RenyiProperties
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Schur concavity of endpoint-aware Renyi entropy

The proof treats finite orders and all three endpoints directly.  In
particular, the order-zero branch proves the support-cardinality inequality
rather than appealing to an unformalized endpoint limit.
-/

noncomputable section

open Set
open scoped BigOperators

namespace ConditionalEntropy

universe u

section

variable {I : Type u} [Fintype I] [Nonempty I]

omit [Nonempty I] in
theorem powerSum_probMatrixAction_ge {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (S : I → I → ℝ) (hS : DoublyStochastic S) (p : ProbVec I) :
    powerSum a p ≤ powerSum a (probMatrixAction S hS p) := by
  have hrow (i : I) :
      (∑ j, S i j * (p.1 j ^ a)) ≤ (matrixAction S p.1 i) ^ a := by
    have hJ := (Real.concaveOn_rpow ha0 ha1).le_map_sum
      (fun j _ => hS.1 i j) (by simpa using hS.2.1 i)
      (fun j _ => p.2.1 j)
    simpa [matrixAction, smul_eq_mul] using hJ
  calc
    powerSum a p = ∑ j, (∑ i, S i j) * (p.1 j ^ a) := by
      simp [powerSum, hS.2.2]
    _ = ∑ i, ∑ j, S i j * (p.1 j ^ a) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ ≤ ∑ i, (matrixAction S p.1 i) ^ a :=
      Finset.sum_le_sum fun i _ => hrow i
    _ = powerSum a (probMatrixAction S hS p) := rfl

omit [Nonempty I] in
theorem powerSum_probMatrixAction_le {a : ℝ} (ha : 1 ≤ a)
    (S : I → I → ℝ) (hS : DoublyStochastic S) (p : ProbVec I) :
    powerSum a (probMatrixAction S hS p) ≤ powerSum a p := by
  have hrow (i : I) :
      (matrixAction S p.1 i) ^ a ≤ ∑ j, S i j * (p.1 j ^ a) := by
    have hJ := (convexOn_rpow ha).map_sum_le
      (fun j _ => hS.1 i j) (by simpa using hS.2.1 i)
      (fun j _ => p.2.1 j)
    simpa [matrixAction, smul_eq_mul] using hJ
  calc
    powerSum a (probMatrixAction S hS p) =
        ∑ i, (matrixAction S p.1 i) ^ a := rfl
    _ ≤ ∑ i, ∑ j, S i j * (p.1 j ^ a) :=
      Finset.sum_le_sum fun i _ => hrow i
    _ = ∑ j, (∑ i, S i j) * (p.1 j ^ a) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ = powerSum a p := by simp [powerSum, hS.2.2]

omit [Nonempty I] in
theorem renyiFinite_probMatrixAction {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1)
    (S : I → I → ℝ) (hS : DoublyStochastic S) (p : ProbVec I) :
    renyiFinite a p ≤ renyiFinite a (probMatrixAction S hS p) := by
  rcases lt_or_gt_of_ne ha1 with halt | hag
  · have hp := powerSum_probMatrixAction_ge ha.le halt.le S hS p
    have hpowp := powerSum_pos ha p
    have hpowq := powerSum_pos ha (probMatrixAction S hS p)
    have hlog : Real.log (powerSum a p) ≤
        Real.log (powerSum a (probMatrixAction S hS p)) :=
      Real.strictMonoOn_log.monotoneOn hpowp hpowq hp
    unfold renyiFinite
    exact div_le_div_of_nonneg_right hlog (sub_nonneg.mpr halt.le)
  · have hp := powerSum_probMatrixAction_le hag.le S hS p
    have hpowp := powerSum_pos ha p
    have hpowq := powerSum_pos ha (probMatrixAction S hS p)
    have hlog : Real.log (powerSum a (probMatrixAction S hS p)) ≤
        Real.log (powerSum a p) :=
      Real.strictMonoOn_log.monotoneOn hpowq hpowp hp
    unfold renyiFinite
    rw [div_le_iff_of_neg (sub_neg.mpr hag)]
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr ha1.symm)]
    exact hlog

omit [Nonempty I] in
theorem renyiOne_probMatrixAction
    (S : I → I → ℝ) (hS : DoublyStochastic S) (p : ProbVec I) :
    renyiOne p ≤ renyiOne (probMatrixAction S hS p) := by
  have hrow (i : I) :
      matrixAction S p.1 i * Real.log (matrixAction S p.1 i) ≤
        ∑ j, S i j * (p.1 j * Real.log (p.1 j)) := by
    have hJ := Real.convexOn_mul_log.map_sum_le
      (fun j _ => hS.1 i j) (by simpa using hS.2.1 i)
      (fun j _ => p.2.1 j)
    simpa [matrixAction, smul_eq_mul] using hJ
  have hsum :
      (∑ i, matrixAction S p.1 i * Real.log (matrixAction S p.1 i)) ≤
        ∑ j, p.1 j * Real.log (p.1 j) := by
    calc
      (∑ i, matrixAction S p.1 i * Real.log (matrixAction S p.1 i)) ≤
          ∑ i, ∑ j, S i j * (p.1 j * Real.log (p.1 j)) :=
        Finset.sum_le_sum fun i _ => hrow i
      _ = ∑ j, (∑ i, S i j) * (p.1 j * Real.log (p.1 j)) := by
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul]
      _ = ∑ j, p.1 j * Real.log (p.1 j) := by simp [hS.2.2]
  unfold renyiOne
  exact neg_le_neg hsum

theorem finMax_probMatrixAction_le
    (S : I → I → ℝ) (hS : DoublyStochastic S) (p : ProbVec I) :
    finMax (probMatrixAction S hS p).1 ≤ finMax p.1 := by
  obtain ⟨i, hi⟩ := finMax_mem (probMatrixAction S hS p).1
  calc
    finMax (probMatrixAction S hS p).1 = matrixAction S p.1 i := hi.symm
    _ ≤ ∑ j, S i j * finMax p.1 := by
      unfold matrixAction
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (le_finMax_apply p.1 j) (hS.1 i j)
    _ = finMax p.1 := by rw [← Finset.sum_mul, hS.2.1 i, one_mul]

theorem renyiTop_probMatrixAction
    (S : I → I → ℝ) (hS : DoublyStochastic S) (p : ProbVec I) :
    renyiTop p ≤ renyiTop (probMatrixAction S hS p) := by
  have hpmax : 0 < finMax p.1 := by
    obtain ⟨i, hi⟩ := exists_prob_pos p
    exact hi.trans_le (le_finMax_apply p.1 i)
  have hqmax : 0 < finMax (probMatrixAction S hS p).1 := by
    obtain ⟨i, hi⟩ := exists_prob_pos (probMatrixAction S hS p)
    exact hi.trans_le (le_finMax_apply _ i)
  have hlog := Real.strictMonoOn_log.monotoneOn hqmax hpmax
    (finMax_probMatrixAction_le S hS p)
  unfold renyiTop
  exact neg_le_neg hlog

omit [Nonempty I] in
theorem support_card_probMatrixAction
    (S : I → I → ℝ) (hS : DoublyStochastic S) (p : ProbVec I) :
    (supportFinset p.1).card ≤
      (supportFinset (probMatrixAction S hS p).1).card := by
  classical
  let q : ProbVec I := probMatrixAction S hS p
  let A : Finset I := supportFinset p.1
  let B : Finset I := supportFinset q.1
  have houtside : ∀ i, i ∉ B → ∀ j, j ∈ A → S i j = 0 := by
    intro i hi j hj
    have hqzero : q.1 i = 0 := by
      simpa [B, supportFinset] using hi
    have hpne : p.1 j ≠ 0 := by
      simpa [A, supportFinset] using hj
    have hterm : S i j * p.1 j ≤ q.1 i := by
      change S i j * p.1 j ≤ ∑ k, S i k * p.1 k
      exact Finset.single_le_sum
        (fun k _ => mul_nonneg (hS.1 i k) (p.2.1 k))
        (Finset.mem_univ j)
    have hprod : S i j * p.1 j = 0 :=
      le_antisymm (by simpa [hqzero] using hterm)
        (mul_nonneg (hS.1 i j) (p.2.1 j))
    exact (mul_eq_zero.mp hprod).resolve_right hpne
  have hrow (i : I) : ∑ j ∈ A, S i j ≤ 1 := by
    calc
      (∑ j ∈ A, S i j) ≤ ∑ j, S i j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
          (fun j _ _ => hS.1 i j)
      _ = 1 := hS.2.1 i
  have hrestrict :
      (∑ i, ∑ j ∈ A, S i j) = ∑ i ∈ B, ∑ j ∈ A, S i j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ B)
    intro i _ hi
    apply Finset.sum_eq_zero
    intro j hj
    exact houtside i hi j hj
  have hcardReal : (A.card : ℝ) ≤ (B.card : ℝ) := by
    calc
      (A.card : ℝ) = ∑ j ∈ A, (1 : ℝ) := by simp
      _ = ∑ j ∈ A, ∑ i, S i j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hS.2.2 j]
      _ = ∑ i, ∑ j ∈ A, S i j := by rw [Finset.sum_comm]
      _ = ∑ i ∈ B, ∑ j ∈ A, S i j := hrestrict
      _ ≤ ∑ i ∈ B, (1 : ℝ) := by
        exact Finset.sum_le_sum fun i _ => hrow i
      _ = (B.card : ℝ) := by simp
  exact_mod_cast hcardReal

omit [Nonempty I] in
theorem renyiZero_probMatrixAction
    (S : I → I → ℝ) (hS : DoublyStochastic S) (p : ProbVec I) :
    renyiZero p ≤ renyiZero (probMatrixAction S hS p) := by
  have hp : 0 < ((supportFinset p.1).card : ℝ) := by
    exact_mod_cast supportFinset_card_pos p
  have hq : 0 < ((supportFinset (probMatrixAction S hS p).1).card : ℝ) := by
    exact_mod_cast supportFinset_card_pos (probMatrixAction S hS p)
  have hcast : ((supportFinset p.1).card : ℝ) ≤
      ((supportFinset (probMatrixAction S hS p).1).card : ℝ) := by
    exact_mod_cast support_card_probMatrixAction S hS p
  unfold renyiZero
  exact Real.strictMonoOn_log.monotoneOn hp hq hcast

/-- Endpoint-aware Renyi entropy is Schur concave under every doubly
stochastic action. -/
theorem renyiSchur (S : I → I → ℝ) (hS : DoublyStochastic S)
    (p : ProbVec I) (alpha : Param) :
    renyi alpha p ≤ renyi alpha (probMatrixAction S hS p) := by
  unfold renyi
  split <;> rename_i htop
  · exact renyiTop_probMatrixAction S hS p
  · split <;> rename_i hzero
    · exact renyiZero_probMatrixAction S hS p
    · split <;> rename_i hone
      · exact renyiOne_probMatrixAction S hS p
      · apply renyiFinite_probMatrixAction
        · exact ENNReal.toReal_pos hzero htop
        · intro ha1
          apply hone
          exact (ENNReal.toReal_eq_one_iff alpha).mp ha1

omit [Nonempty I] in
theorem powerSum_mix_ge {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (p q : ProbVec I) (lambda : ℝ) (hlambda : lambda ∈ Icc (0 : ℝ) 1) :
    lambda * powerSum a p + (1 - lambda) * powerSum a q ≤
      powerSum a (mixProbVec lambda hlambda p q) := by
  unfold powerSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hcoord := (Real.concaveOn_rpow ha0 ha1).2
    (show p.1 i ∈ Ici (0 : ℝ) from p.2.1 i)
    (show q.1 i ∈ Ici (0 : ℝ) from q.2.1 i)
    hlambda.1 (sub_nonneg.mpr hlambda.2)
  simpa [mixProbVec, add_comm, add_left_comm, add_assoc] using hcoord

omit [Nonempty I] in
theorem renyiFinite_simplexConcave {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    SimplexConcave (renyiFinite a : ProbVec I → ℝ) := by
  intro p q lambda hlambda
  have hpowMix := powerSum_mix_ge ha.le ha1.le p q lambda hlambda
  have hp : 0 < powerSum a p := powerSum_pos ha p
  have hq : 0 < powerSum a q := powerSum_pos ha q
  have hweighted : 0 < lambda * powerSum a p +
      (1 - lambda) * powerSum a q := by
    rcases hlambda.1.eq_or_lt with rfl | hlpos
    · simpa using hq
    · exact add_pos_of_pos_of_nonneg (mul_pos hlpos hp)
        (mul_nonneg (sub_nonneg.mpr hlambda.2) hq.le)
  have hmix : 0 < powerSum a (mixProbVec lambda hlambda p q) :=
    powerSum_pos ha _
  have hlogMono :
      Real.log (lambda * powerSum a p + (1 - lambda) * powerSum a q) ≤
        Real.log (powerSum a (mixProbVec lambda hlambda p q)) :=
    Real.strictMonoOn_log.monotoneOn hweighted hmix hpowMix
  have hlogConcave := strictConcaveOn_log_Ioi.concaveOn.2
    (show powerSum a q ∈ Ioi (0 : ℝ) from hq)
    (show powerSum a p ∈ Ioi (0 : ℝ) from hp)
    (sub_nonneg.mpr hlambda.2) hlambda.1 (by ring)
  simp only [smul_eq_mul] at hlogConcave
  have hlogs : lambda * Real.log (powerSum a p) +
      (1 - lambda) * Real.log (powerSum a q) ≤
        Real.log (powerSum a (mixProbVec lambda hlambda p q)) := by
    calc
      lambda * Real.log (powerSum a p) +
          (1 - lambda) * Real.log (powerSum a q) =
        (1 - lambda) * Real.log (powerSum a q) +
          lambda * Real.log (powerSum a p) := by ring
      _ ≤ Real.log ((1 - lambda) * powerSum a q +
          lambda * powerSum a p) := hlogConcave
      _ = Real.log (lambda * powerSum a p +
          (1 - lambda) * powerSum a q) := by ring_nf
      _ ≤ Real.log (powerSum a (mixProbVec lambda hlambda p q)) := hlogMono
  unfold renyiFinite
  calc
    lambda * (Real.log (powerSum a p) / (1 - a)) +
        (1 - lambda) * (Real.log (powerSum a q) / (1 - a)) =
      (lambda * Real.log (powerSum a p) +
        (1 - lambda) * Real.log (powerSum a q)) / (1 - a) := by ring
    _ ≤ Real.log (powerSum a (mixProbVec lambda hlambda p q)) / (1 - a) :=
      (div_le_div_iff_of_pos_right (sub_pos.mpr ha1)).2 hlogs

omit [Nonempty I] in
theorem renyiOne_simplexConcave :
    SimplexConcave (renyiOne : ProbVec I → ℝ) := by
  intro p q lambda hlambda
  unfold renyiOne
  simp only [← Finset.sum_neg_distrib]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hcoord := Real.concaveOn_negMulLog.2
    (show p.1 i ∈ Ici (0 : ℝ) from p.2.1 i)
    (show q.1 i ∈ Ici (0 : ℝ) from q.2.1 i)
    hlambda.1 (sub_nonneg.mpr hlambda.2) (by ring)
  simp only [Real.negMulLog_def, smul_eq_mul] at hcoord
  simp only [mixProbVec]
  convert hcoord using 1 <;> ring

omit [Nonempty I] in
theorem renyiZero_simplexConcave :
    SimplexConcave (renyiZero : ProbVec I → ℝ) := by
  intro p q lambda hlambda
  by_cases hl0 : lambda = 0
  · subst lambda
    simp [mixProbVec]
  by_cases hl1 : lambda = 1
  · subst lambda
    simp [mixProbVec]
  have hlpos : 0 < lambda := lt_of_le_of_ne hlambda.1 (Ne.symm hl0)
  have hllt : lambda < 1 := lt_of_le_of_ne hlambda.2 hl1
  let r := mixProbVec lambda hlambda p q
  have hpSub : supportFinset p.1 ⊆ supportFinset r.1 := by
    intro i hi
    have hpne : p.1 i ≠ 0 := by simpa [supportFinset] using hi
    have hppos : 0 < p.1 i := lt_of_le_of_ne (p.2.1 i) (Ne.symm hpne)
    have hrpos : 0 < r.1 i := by
      exact add_pos_of_pos_of_nonneg (mul_pos hlpos hppos)
        (mul_nonneg (sub_nonneg.mpr hlambda.2) (q.2.1 i))
    simpa [supportFinset] using hrpos.ne'
  have hqSub : supportFinset q.1 ⊆ supportFinset r.1 := by
    intro i hi
    have hqne : q.1 i ≠ 0 := by simpa [supportFinset] using hi
    have hqpos : 0 < q.1 i := lt_of_le_of_ne (q.2.1 i) (Ne.symm hqne)
    have hrpos : 0 < r.1 i := by
      exact add_pos_of_nonneg_of_pos (mul_nonneg hlambda.1 (p.2.1 i))
        (mul_pos (sub_pos.mpr hllt) hqpos)
    simpa [supportFinset] using hrpos.ne'
  have hpCard := Finset.card_le_card hpSub
  have hqCard := Finset.card_le_card hqSub
  have hrCardPos : 0 < ((supportFinset r.1).card : ℝ) := by
    exact_mod_cast supportFinset_card_pos r
  have hpCardPos : 0 < ((supportFinset p.1).card : ℝ) := by
    exact_mod_cast supportFinset_card_pos p
  have hqCardPos : 0 < ((supportFinset q.1).card : ℝ) := by
    exact_mod_cast supportFinset_card_pos q
  have hpLog : renyiZero p ≤ renyiZero r := by
    unfold renyiZero
    exact Real.strictMonoOn_log.monotoneOn hpCardPos hrCardPos (by exact_mod_cast hpCard)
  have hqLog : renyiZero q ≤ renyiZero r := by
    unfold renyiZero
    exact Real.strictMonoOn_log.monotoneOn hqCardPos hrCardPos (by exact_mod_cast hqCard)
  change lambda * renyiZero p + (1 - lambda) * renyiZero q ≤ renyiZero r
  calc
    lambda * renyiZero p + (1 - lambda) * renyiZero q ≤
        lambda * renyiZero r + (1 - lambda) * renyiZero r :=
      add_le_add (mul_le_mul_of_nonneg_left hpLog hlambda.1)
        (mul_le_mul_of_nonneg_left hqLog (sub_nonneg.mpr hlambda.2))
    _ = renyiZero r := by ring

/-- Every endpoint-aware Renyi entropy of order at most one is concave on the
probability simplex. -/
theorem renyiSimplexConcave (alpha : Param) (halpha : alpha ≤ 1) :
    SimplexConcave (renyi alpha : ProbVec I → ℝ) := by
  unfold renyi
  split <;> rename_i htop
  · subst alpha
    simp at halpha
  · split <;> rename_i hzero
    · exact renyiZero_simplexConcave
    · split <;> rename_i hone
      · exact renyiOne_simplexConcave
      · apply renyiFinite_simplexConcave
        · exact ENNReal.toReal_pos hzero htop
        · have hrealLe : ENNReal.toReal alpha ≤ 1 := by
            simpa using ENNReal.toReal_mono ENNReal.one_ne_top halpha
          exact lt_of_le_of_ne hrealLe (fun heq =>
            hone ((ENNReal.toReal_eq_one_iff alpha).mp heq))

end

end ConditionalEntropy
