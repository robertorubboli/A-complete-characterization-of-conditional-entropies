import ConditionalEntropy.Renyi

/-!
# Closed algebraic properties of endpoint-aware Renyi entropy

This module proves the finite algebra needed by the manuscript directly from
the total definition in `ConditionalEntropy.Renyi`.  In particular, every
endpoint is handled explicitly; none of the declarations below assumes an
analytic continuation theorem.
-/

noncomputable section

open Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u v

section Elementary

variable {I : Type u} [Fintype I] [Nonempty I]

omit [Nonempty I] in
/-- Every coordinate of a finite probability vector is at most one. -/
theorem probVec_apply_le_one (p : ProbVec I) (i : I) : p.1 i ≤ 1 := by
  have hi : p.1 i ≤ ∑ j, p.1 j :=
    Finset.single_le_sum (fun j _ => p.2.1 j) (Finset.mem_univ i)
  simpa only [l1Mass] using hi.trans_eq p.2.2

omit [Nonempty I] in
/-- The finite support of a probability vector is nonempty. -/
theorem supportFinset_nonempty (p : ProbVec I) : (supportFinset p.1).Nonempty := by
  obtain ⟨i, hi⟩ := exists_prob_pos p
  exact ⟨i, by simp [supportFinset, hi.ne']⟩

omit [Nonempty I] in
/-- Consequently, the cardinality of the support is positive. -/
theorem supportFinset_card_pos (p : ProbVec I) : 0 < (supportFinset p.1).card :=
  (supportFinset_nonempty p).card_pos

/-- Every coordinate is bounded above by the finite maximum. -/
theorem le_finMax (p : ProbVec I) (i : I) : p.1 i ≤ finMax p.1 := by
  exact Finset.le_sup' p.1 (Finset.mem_univ i)

/-- The maximum coordinate of a probability vector is positive. -/
theorem finMax_pos (p : ProbVec I) : 0 < finMax p.1 := by
  obtain ⟨i, hi⟩ := exists_prob_pos p
  exact hi.trans_le (le_finMax p i)

/-- The maximum coordinate of a probability vector is at most one. -/
theorem finMax_le_one (p : ProbVec I) : finMax p.1 ≤ 1 := by
  apply Finset.sup'_le Finset.univ_nonempty
  intro i _
  exact probVec_apply_le_one p i

omit [Nonempty I] in
/-- The Shannon summand is nonnegative on a probability vector. -/
theorem shannonSummand_nonneg (p : ProbVec I) (i : I) :
    0 ≤ -(p.1 i * Real.log (p.1 i)) := by
  by_cases hi : p.1 i = 0
  · simp [hi]
  · have hipos : 0 < p.1 i := lt_of_le_of_ne (p.2.1 i) (Ne.symm hi)
    have hilog : Real.log (p.1 i) ≤ 0 :=
      Real.log_nonpos (hipos.le) (probVec_apply_le_one p i)
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hipos.le hilog)

omit [Nonempty I] in
/-- Shannon entropy is nonnegative. -/
theorem renyiOne_nonneg (p : ProbVec I) : 0 ≤ renyiOne p := by
  simpa only [renyiOne, Finset.sum_neg_distrib] using
    (Finset.sum_nonneg fun i (_hi : i ∈ Finset.univ) => shannonSummand_nonneg p i)

omit [Nonempty I] in
/-- Order-zero entropy is nonnegative. -/
theorem renyiZero_nonneg (p : ProbVec I) : 0 ≤ renyiZero p := by
  rw [renyiZero]
  exact Real.log_nonneg (by exact_mod_cast (supportFinset_card_pos p))

/-- Min-entropy is nonnegative. -/
theorem renyiTop_nonneg (p : ProbVec I) : 0 ≤ renyiTop p := by
  rw [renyiTop]
  exact neg_nonneg.mpr (Real.log_nonpos (finMax_pos p).le (finMax_le_one p))

/-- Order-zero entropy is bounded by the logarithm of the ambient cardinality. -/
theorem renyiZero_le_log_card (p : ProbVec I) :
    renyiZero p ≤ Real.log (Fintype.card I : ℝ) := by
  have hspos : 0 < ((supportFinset p.1).card : ℝ) := by
    exact_mod_cast supportFinset_card_pos p
  have hnpos : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcard : ((supportFinset p.1).card : ℝ) ≤ (Fintype.card I : ℝ) := by
    exact_mod_cast Finset.card_le_univ (s := supportFinset p.1)
  exact Real.strictMonoOn_log.monotoneOn hspos hnpos hcard

/-- The largest coordinate is at least the uniform coordinate. -/
theorem inv_card_le_finMax (p : ProbVec I) :
    (Fintype.card I : ℝ)⁻¹ ≤ finMax p.1 := by
  have hnpos : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hmass : ∑ i, p.1 i = 1 := by simpa only [l1Mass] using p.2.2
  have hsum : ∑ i, p.1 i ≤ ∑ _i : I, finMax p.1 :=
    Finset.sum_le_sum fun i _ => le_finMax p i
  have hone : 1 ≤ (Fintype.card I : ℝ) * finMax p.1 := by
    simpa [hmass, nsmul_eq_mul] using hsum
  rw [← one_div]
  exact (div_le_iff₀ hnpos).2 (by simpa [mul_comm] using hone)

/-- Min-entropy is bounded by the logarithm of the ambient cardinality. -/
theorem renyiTop_le_log_card (p : ProbVec I) :
    renyiTop p ≤ Real.log (Fintype.card I : ℝ) := by
  have hnpos : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hinvpos : 0 < (Fintype.card I : ℝ)⁻¹ := inv_pos.mpr hnpos
  have hlog := Real.strictMonoOn_log.monotoneOn hinvpos (finMax_pos p)
    (inv_card_le_finMax p)
  rw [Real.log_inv] at hlog
  simpa [renyiTop] using (neg_le_neg hlog)

omit [Nonempty I] in
/-- Below the Shannon order, every coordinate is bounded above by its real
power. -/
theorem powerSum_one_le_of_le_one (p : ProbVec I) {a : ℝ}
    (_ha : 0 ≤ a) (ha1 : a ≤ 1) : 1 ≤ powerSum a p := by
  have hmass : ∑ i, p.1 i = 1 := by simpa only [l1Mass] using p.2.2
  rw [← hmass, powerSum]
  exact Finset.sum_le_sum fun i _ =>
    Real.self_le_rpow_of_le_one (p.2.1 i) (probVec_apply_le_one p i) ha1

omit [Nonempty I] in
/-- Above the Shannon order, every powered coordinate is bounded above by
the original coordinate. -/
theorem powerSum_le_one_of_one_le (p : ProbVec I) {a : ℝ} (ha1 : 1 ≤ a) :
    powerSum a p ≤ 1 := by
  have hmass : ∑ i, p.1 i = 1 := by simpa only [l1Mass] using p.2.2
  rw [← hmass, powerSum]
  exact Finset.sum_le_sum fun i _ =>
    Real.rpow_le_self_of_le_one (p.2.1 i) (probVec_apply_le_one p i) ha1

omit [Nonempty I] in
/-- Nonnegativity of the finite formula below order one. -/
theorem renyiFinite_nonneg_of_lt_one (p : ProbVec I) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) : 0 ≤ renyiFinite a p := by
  have hsum : 1 ≤ powerSum a p := powerSum_one_le_of_le_one p ha.le ha1.le
  exact div_nonneg (Real.log_nonneg hsum) (sub_nonneg.mpr ha1.le)

omit [Nonempty I] in
/-- Nonnegativity of the finite formula above order one. -/
theorem renyiFinite_nonneg_of_one_lt (p : ProbVec I) {a : ℝ}
    (ha1 : 1 < a) : 0 ≤ renyiFinite a p := by
  have hsum : powerSum a p ≤ 1 := powerSum_le_one_of_one_le p ha1.le
  have hlog : Real.log (powerSum a p) ≤ 0 :=
    Real.log_nonpos (powerSum_pos (lt_trans zero_lt_one ha1) p).le hsum
  exact div_nonneg_of_nonpos hlog (sub_nonpos.mpr ha1.le)

/-- Endpoint-aware Renyi entropy is nonnegative at every order. -/
theorem renyi_nonneg (a : Param) (p : ProbVec I) : 0 ≤ renyi a p := by
  by_cases htop : a = (⊤ : Param)
  · simpa [htop] using renyiTop_nonneg p
  by_cases hzero : a = (0 : Param)
  · simpa [hzero] using renyiZero_nonneg p
  by_cases hone : a = (1 : Param)
  · simpa [hone] using renyiOne_nonneg p
  have hrpos : 0 < paramToReal a htop := ENNReal.toReal_pos hzero htop
  have hr1 : paramToReal a htop ≠ 1 := by
    intro hr
    apply hone
    rw [← finiteParam_paramToReal a htop, hr, finiteParam_one]
  have hfinite : 0 ≤ renyiFinite (paramToReal a htop) p := by
    rcases lt_or_gt_of_ne hr1 with hlt | hgt
    · exact renyiFinite_nonneg_of_lt_one p hrpos hlt
    · exact renyiFinite_nonneg_of_one_lt p hgt
  simpa [renyi, htop, hzero, hone] using hfinite

omit [Nonempty I] in
/-- The finite-order formula is continuous at every positive non-Shannon
order.  This is the interior analytic part of order continuity; the endpoint
limits are intentionally separate statements. -/
theorem continuousAt_renyiFinite (p : ProbVec I) {a : ℝ}
    (ha : 0 < a) (ha1 : a ≠ 1) :
    ContinuousAt (fun b => renyiFinite b p) a := by
  have hpow : ContinuousAt (fun b => powerSum b p) a := by
    unfold powerSum
    exact tendsto_finsetSum Finset.univ fun i _ =>
      Real.continuousAt_const_rpow' ha.ne'
  have hlog : ContinuousAt (fun b => Real.log (powerSum b p)) a :=
    hpow.log (powerSum_pos ha p).ne'
  have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  exact hlog.div (continuousAt_const.sub continuousAt_id) hden

end Elementary

section EmbeddingFacts

variable {I : Type u} [Fintype I]

/-- A function vanishing at zero sums over a zero extension exactly as it
sums over the original finite type. -/
theorem sum_comp_zeroExtendRaw {J : Type v} [Fintype J]
    (e : I ↪ J) (x : I → ℝ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    ∑ j, f (zeroExtendRaw e x j) = ∑ i, f (x i) := by
  classical
  calc
    ∑ j : J, f (zeroExtendRaw e x j) =
        ∑ j ∈ Finset.univ.map e, f (zeroExtendRaw e x j) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have hrange : j ∉ Set.range e := by
        rintro ⟨i, rfl⟩
        exact hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      simp [zeroExtendRaw, hrange, hf]
    _ = ∑ i : I, f (x i) := by simp

/-- The support itself is transported by an embedding under zero extension. -/
theorem supportFinset_zeroExtendRaw {J : Type v} [Fintype J]
    (e : I ↪ J) (x : I → ℝ) :
    supportFinset (zeroExtendRaw e x) = (supportFinset x).map e := by
  classical
  ext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    simp [supportFinset]
  · constructor
    · intro h
      have hzero : zeroExtendRaw e x j = 0 := by simp [zeroExtendRaw, hj]
      simp [supportFinset, hzero] at h
    · intro h
      obtain ⟨i, _hi, hij⟩ := Finset.mem_map.mp h
      exact (hj ⟨i, hij⟩).elim

/-- Zero extension preserves support cardinality. -/
theorem supportFinset_zeroExtendRaw_card {J : Type v} [Fintype J]
    (e : I ↪ J) (x : I → ℝ) :
    (supportFinset (zeroExtendRaw e x)).card = (supportFinset x).card := by
  rw [supportFinset_zeroExtendRaw]
  exact Finset.card_map _

/-- Positive-order power sums are invariant under zero extension. -/
theorem powerSum_zeroExtend {J : Type v} [Fintype J]
    (e : I ↪ J) (p : ProbVec I) {a : ℝ} (ha : 0 < a) :
    powerSum a (zeroExtendProb e p) = powerSum a p := by
  unfold powerSum zeroExtendProb
  exact sum_comp_zeroExtendRaw e p.1 (fun z => z ^ a) (by simp [ha.ne'])

/-- Shannon entropy is invariant under zero extension. -/
theorem renyiOne_zeroExtend {J : Type v} [Fintype J]
    (e : I ↪ J) (p : ProbVec I) :
    renyiOne (zeroExtendProb e p) = renyiOne p := by
  unfold renyiOne zeroExtendProb
  rw [sum_comp_zeroExtendRaw e p.1 (fun z => z * Real.log z) (by simp)]

/-- Hartley entropy is invariant under zero extension. -/
theorem renyiZero_zeroExtend {J : Type v} [Fintype J]
    (e : I ↪ J) (p : ProbVec I) :
    renyiZero (zeroExtendProb e p) = renyiZero p := by
  change Real.log ((supportFinset (zeroExtendRaw e p.1)).card : ℝ) =
    Real.log ((supportFinset p.1).card : ℝ)
  rw [supportFinset_zeroExtendRaw_card]

/-- A nonnegative finite family and its zero extension have the same maximum. -/
theorem finMax_zeroExtendRaw {J : Type v} [Fintype J] [Nonempty I] [Nonempty J]
    (e : I ↪ J) (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    finMax (zeroExtendRaw e x) = finMax x := by
  classical
  apply le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
    intro j _
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      rw [zeroExtendRaw_apply]
      change x i ≤ Finset.univ.sup' Finset.univ_nonempty x
      exact Finset.le_sup' x (Finset.mem_univ i)
    · rw [zeroExtendRaw, dif_neg hj]
      let i : I := Classical.choice inferInstance
      exact (hx i).trans (Finset.le_sup' x (Finset.mem_univ i))
  · apply Finset.sup'_le Finset.univ_nonempty
    intro i _
    change x i ≤ Finset.univ.sup' Finset.univ_nonempty (zeroExtendRaw e x)
    calc
      x i = zeroExtendRaw e x (e i) := (zeroExtendRaw_apply e x i).symm
      _ ≤ Finset.univ.sup' Finset.univ_nonempty (zeroExtendRaw e x) :=
        Finset.le_sup' (zeroExtendRaw e x) (Finset.mem_univ (e i))

/-- Min-entropy is invariant under zero extension. -/
theorem renyiTop_zeroExtend {J : Type v} [Fintype J] [Nonempty I] [Nonempty J]
    (e : I ↪ J) (p : ProbVec I) :
    renyiTop (zeroExtendProb e p) = renyiTop p := by
  simp [renyiTop, zeroExtendProb, finMax_zeroExtendRaw e p.1 p.2.1]

/-- The ordinary positive finite-order formula is invariant under zero extension. -/
theorem renyiFinite_zeroExtend {J : Type v} [Fintype J]
    (e : I ↪ J) (p : ProbVec I) {a : ℝ} (ha : 0 < a) :
    renyiFinite a (zeroExtendProb e p) = renyiFinite a p := by
  simp [renyiFinite, powerSum_zeroExtend e p ha]

/-- Endpoint-aware Renyi entropy is invariant under every finite zero
embedding. -/
theorem renyi_zeroExtend {J : Type v} [Fintype J] [Nonempty I] [Nonempty J]
    (a : Param) (e : I ↪ J) (p : ProbVec I) :
    renyi a (zeroExtendProb e p) = renyi a p := by
  by_cases htop : a = (⊤ : Param)
  · simp [htop, renyiTop_zeroExtend]
  by_cases hzero : a = (0 : Param)
  · simp [hzero, renyiZero_zeroExtend]
  by_cases hone : a = (1 : Param)
  · simp [hone, renyiOne_zeroExtend]
  have hrpos : 0 < paramToReal a htop := ENNReal.toReal_pos hzero htop
  simp [renyi, htop, hzero, hone, renyiFinite_zeroExtend e p hrpos]

/-- Literal relabeling/embedding package requested by the blueprint. -/
theorem renyi_embedding {J : Type v} [Fintype J] [Nonempty I] [Nonempty J]
    (p : ProbVec I) (e : I ↪ J) (r : I ≃ J) (a : Param) :
    renyi a (zeroExtendProb e p) = renyi a p ∧
      renyi a (zeroExtendProb r.toEmbedding p) = renyi a p := by
  exact ⟨renyi_zeroExtend a e p, renyi_zeroExtend a r.toEmbedding p⟩

end EmbeddingFacts

section TensorFacts

variable {I : Type u} [Fintype I] [Nonempty I]
variable {J : Type v} [Fintype J] [Nonempty J]

omit [Nonempty I] [Nonempty J] in
/-- The support of a tensor product is the product of the supports. -/
theorem supportFinset_probTensor (p : ProbVec I) (q : ProbVec J) :
    supportFinset (probTensor p q).1 =
      (supportFinset p.1).product (supportFinset q.1) := by
  classical
  ext z
  simp [supportFinset, probTensor]

omit [Nonempty I] [Nonempty J] in
/-- Support cardinalities multiply under tensor products. -/
theorem supportFinset_probTensor_card (p : ProbVec I) (q : ProbVec J) :
    (supportFinset (probTensor p q).1).card =
      (supportFinset p.1).card * (supportFinset q.1).card := by
  rw [supportFinset_probTensor]
  exact Finset.card_product _ _

/-- Finite maxima multiply under tensor products of probability vectors. -/
theorem finMax_probTensor (p : ProbVec I) (q : ProbVec J) :
    finMax (probTensor p q).1 = finMax p.1 * finMax q.1 := by
  apply le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
    rintro ⟨i, j⟩ _
    exact mul_le_mul (le_finMax p i) (le_finMax q j) (q.2.1 j)
      (le_of_lt (finMax_pos p))
  · obtain ⟨i, hi⟩ := finMax_mem p.1
    obtain ⟨j, hj⟩ := finMax_mem q.1
    rw [← hi, ← hj]
    change p.1 i * q.1 j ≤
      Finset.univ.sup' Finset.univ_nonempty (fun z : I × J => (probTensor p q).1 z)
    exact Finset.le_sup' (fun z : I × J => (probTensor p q).1 z)
      (Finset.mem_univ (i, j))

omit [Nonempty I] [Nonempty J] in
/-- Hartley entropy is additive under tensor products. -/
theorem renyiZero_tensor (p : ProbVec I) (q : ProbVec J) :
    renyiZero (probTensor p q) = renyiZero p + renyiZero q := by
  rw [renyiZero, renyiZero, renyiZero, supportFinset_probTensor_card]
  rw [Nat.cast_mul, Real.log_mul]
  · exact_mod_cast (supportFinset_card_pos p).ne'
  · exact_mod_cast (supportFinset_card_pos q).ne'

/-- The logarithmic Shannon summand splits across a product, including its
zero-coordinate cases. -/
theorem mul_log_mul (x y : ℝ) (_hx : 0 ≤ x) (_hy : 0 ≤ y) :
    x * y * Real.log (x * y) =
      y * (x * Real.log x) + x * (y * Real.log y) := by
  by_cases hxy : x = 0
  · simp [hxy]
  by_cases hyy : y = 0
  · simp [hyy]
  rw [Real.log_mul hxy hyy]
  ring

omit [Nonempty I] [Nonempty J] in
/-- Shannon entropy is additive under tensor products. -/
theorem renyiOne_tensor (p : ProbVec I) (q : ProbVec J) :
    renyiOne (probTensor p q) = renyiOne p + renyiOne q := by
  have hp : ∑ i, p.1 i = 1 := by simpa only [l1Mass] using p.2.2
  have hq : ∑ j, q.1 j = 1 := by simpa only [l1Mass] using q.2.2
  simp only [renyiOne, probTensor, Fintype.sum_prod_type]
  simp_rw [mul_log_mul _ _ (p.2.1 _) (q.2.1 _)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hp, hq]
  ring

/-- Min-entropy is additive under tensor products. -/
theorem renyiTop_tensor (p : ProbVec I) (q : ProbVec J) :
    renyiTop (probTensor p q) = renyiTop p + renyiTop q := by
  simp only [renyiTop, finMax_probTensor]
  rw [Real.log_mul (finMax_pos p).ne' (finMax_pos q).ne']
  ring

omit [Nonempty I] [Nonempty J] in
/-- The ordinary positive finite-order formula is additive under tensor
products. -/
theorem renyiFinite_tensor (p : ProbVec I) (q : ProbVec J)
    {a : ℝ} (ha : 0 < a) :
    renyiFinite a (probTensor p q) = renyiFinite a p + renyiFinite a q := by
  simp only [renyiFinite, powerSum_tensor]
  rw [Real.log_mul (powerSum_pos ha p).ne' (powerSum_pos ha q).ne']
  ring

/-- Endpoint-aware Renyi entropy is additive under tensor products. -/
theorem renyi_tensor (a : Param) (p : ProbVec I) (q : ProbVec J) :
    renyi a (probTensor p q) = renyi a p + renyi a q := by
  by_cases htop : a = (⊤ : Param)
  · simp [htop, renyiTop_tensor]
  by_cases hzero : a = (0 : Param)
  · simp [hzero, renyiZero_tensor]
  by_cases hone : a = (1 : Param)
  · simp [hone, renyiOne_tensor]
  have hrpos : 0 < paramToReal a htop := ENNReal.toReal_pos hzero htop
  simp [renyi, htop, hzero, hone, renyiFinite_tensor p q hrpos]

end TensorFacts

section UniformFacts

variable {I : Type u} [Fintype I] [Nonempty I]

/-- The support of a uniform probability vector is the whole type. -/
@[simp] theorem supportFinset_uniformProb :
    supportFinset (uniformProb (I := I)).1 = Finset.univ := by
  classical
  ext i
  simp [supportFinset, uniformProb, Fintype.card_ne_zero]

/-- The maximum coordinate of a uniform probability vector. -/
@[simp] theorem finMax_uniformProb :
    finMax (uniformProb (I := I)).1 = (Fintype.card I : ℝ)⁻¹ := by
  change Finset.univ.sup' Finset.univ_nonempty
      (fun _ : I => (Fintype.card I : ℝ)⁻¹) = (Fintype.card I : ℝ)⁻¹
  exact Finset.sup'_const Finset.univ_nonempty _

/-- The power sum of a uniform probability vector. -/
theorem powerSum_uniformProb (a : ℝ) :
    powerSum a (uniformProb (I := I)) =
      (Fintype.card I : ℝ) * (Fintype.card I : ℝ)⁻¹ ^ a := by
  simp [powerSum, uniformProb, nsmul_eq_mul]

/-- Hartley entropy of a uniform probability vector. -/
@[simp] theorem renyiZero_uniformProb :
    renyiZero (uniformProb (I := I)) = Real.log (Fintype.card I : ℝ) := by
  simp [renyiZero]

/-- Shannon entropy of a uniform probability vector. -/
@[simp] theorem renyiOne_uniformProb :
    renyiOne (uniformProb (I := I)) = Real.log (Fintype.card I : ℝ) := by
  have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [renyiOne, uniformProb, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Real.log_inv]
  field_simp

/-- Min-entropy of a uniform probability vector. -/
@[simp] theorem renyiTop_uniformProb :
    renyiTop (uniformProb (I := I)) = Real.log (Fintype.card I : ℝ) := by
  simp [renyiTop, Real.log_inv]

/-- Every non-Shannon finite-order formula has the expected uniform value. -/
theorem renyiFinite_uniformProb (a : ℝ) (ha1 : a ≠ 1) :
    renyiFinite a (uniformProb (I := I)) = Real.log (Fintype.card I : ℝ) := by
  have hnpos : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hn : (Fintype.card I : ℝ) ≠ 0 := hnpos.ne'
  have hinvpos : 0 < (Fintype.card I : ℝ)⁻¹ := inv_pos.mpr hnpos
  have hp : 0 < (Fintype.card I : ℝ)⁻¹ ^ a := Real.rpow_pos_of_pos hinvpos a
  have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  rw [renyiFinite, powerSum_uniformProb]
  rw [Real.log_mul hn hp.ne', Real.log_rpow hinvpos, Real.log_inv]
  field_simp [hden]
  ring

/-- Uniform distributions have entropy equal to the logarithm of their
cardinality at every compactified order. -/
theorem renyi_uniformProb (a : Param) :
    renyi a (uniformProb (I := I)) = Real.log (Fintype.card I : ℝ) := by
  by_cases htop : a = (⊤ : Param)
  · simp [htop]
  by_cases hzero : a = (0 : Param)
  · simp [hzero]
  by_cases hone : a = (1 : Param)
  · simp [hone]
  have hr1 : paramToReal a htop ≠ 1 := by
    intro hr
    apply hone
    rw [← finiteParam_paramToReal a htop, hr, finiteParam_one]
  simp [renyi, htop, hzero, hone, renyiFinite_uniformProb (I := I) _ hr1]

/-- Blueprint form of the uniform-distribution theorem for `Fin d`. -/
theorem renyi_uniform (d : ℕ) (hd : 0 < d) (a : Param) :
    letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    renyi a (uniformProb (I := Fin d)) = Real.log (d : ℝ) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  simpa using renyi_uniformProb (I := Fin d) a

/-- Natural-log normalization of a fair bit. -/
@[simp] theorem renyi_uniform_bit (a : Param) :
    renyi a (uniformProb (I := Fin 2)) = Real.log 2 := by
  simpa using renyi_uniform 2 (by norm_num) a

end UniformFacts

end ConditionalEntropy
