import ConditionalEntropy.ShapeReduction
import ConditionalEntropy.FiniteExtrema

/-!
# Tropical conditional-channel shape reductions

This module supplies the finite quasi-mixing layer for punctured cone
functions and uses it to prove the exact tropical channel/shape
equivalences.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace ConditionalEntropy

universe u v w

/-! ## Binary and finite quasi-mixing -/

/-- Scale invariance turns binary quasi-convexity into a rule for ordinary
addition of two nonzero cone vectors. -/
theorem qcvx_coneAdd
    {I : Type u} (f : PosConeVec I → ℝ)
    (hscale : ScaleInvariant f) (hqcvx : QCvx f)
    (x z : ConeVec I) (hx : x ≠ 0) (hz : z ≠ 0) :
    f (toPosCone (x + z) (by
      intro hsum
      apply hx
      apply Subtype.ext
      funext i
      have hi := congrArg (fun q : ConeVec I => q.1 i) hsum
      have hxi : x.1 i ≤ x.1 i + z.1 i :=
        le_add_of_nonneg_right (z.2 i)
      exact le_antisymm (by simpa using hxi.trans_eq hi) (x.2 i))) ≤
      max (f (toPosCone x hx)) (f (toPosCone z hz)) := by
  let hhalf : 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 := by norm_num
  let m := posMix (1 / 2 : ℝ) hhalf (toPosCone x hx) (toPosCone z hz)
  have hsum : x + z ≠ 0 := by
    intro hzero
    apply hx
    apply Subtype.ext
    funext i
    have hi := congrArg (fun q : ConeVec I => q.1 i) hzero
    have hxi : x.1 i ≤ x.1 i + z.1 i :=
      le_add_of_nonneg_right (z.2 i)
    exact le_antisymm (by simpa using hxi.trans_eq hi) (x.2 i)
  have heq : posScale 2 (by norm_num) m = toPosCone (x + z) hsum := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change 2 * ((1 / 2 : ℝ) * x.1 i + (1 - 1 / 2) * z.1 i) =
      x.1 i + z.1 i
    ring
  calc
    f (toPosCone (x + z) hsum) = f (posScale 2 (by norm_num) m) :=
      congrArg f heq.symm
    _ = f m := hscale m 2 (by norm_num)
    _ ≤ max (f (toPosCone x hx)) (f (toPosCone z hz)) :=
      hqcvx (toPosCone x hx) (toPosCone z hz) (1 / 2 : ℝ) hhalf

/-- Scale invariance turns max-quasi-concavity into a rule for ordinary
addition of two nonzero cone vectors. -/
theorem maxQCave_coneAdd
    {I : Type u} (f : PosConeVec I → ℝ)
    (hscale : ScaleInvariant f) (hmax : MaxQCave f)
    (x z : ConeVec I) (hx : x ≠ 0) (hz : z ≠ 0) :
    max (f (toPosCone x hx)) (f (toPosCone z hz)) ≤
      f (toPosCone (x + z) (by
        intro hsum
        apply hx
        apply Subtype.ext
        funext i
        have hi := congrArg (fun q : ConeVec I => q.1 i) hsum
        have hxi : x.1 i ≤ x.1 i + z.1 i :=
          le_add_of_nonneg_right (z.2 i)
        exact le_antisymm (by simpa using hxi.trans_eq hi) (x.2 i))) := by
  let hhalf : 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 := by norm_num
  let m := posMix (1 / 2 : ℝ) hhalf (toPosCone x hx) (toPosCone z hz)
  have hsum : x + z ≠ 0 := by
    intro hzero
    apply hx
    apply Subtype.ext
    funext i
    have hi := congrArg (fun q : ConeVec I => q.1 i) hzero
    have hxi : x.1 i ≤ x.1 i + z.1 i :=
      le_add_of_nonneg_right (z.2 i)
    exact le_antisymm (by simpa using hxi.trans_eq hi) (x.2 i)
  have heq : posScale 2 (by norm_num) m = toPosCone (x + z) hsum := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change 2 * ((1 / 2 : ℝ) * x.1 i + (1 - 1 / 2) * z.1 i) =
      x.1 i + z.1 i
    ring
  calc
    max (f (toPosCone x hx)) (f (toPosCone z hz)) ≤ f m :=
      hmax (toPosCone x hx) (toPosCone z hz) (1 / 2 : ℝ) hhalf
    _ = f (posScale 2 (by norm_num) m) := (hscale m 2 (by norm_num)).symm
    _ = f (toPosCone (x + z) hsum) := congrArg f heq

/-- A finite cone sum is nonzero when it contains a nonzero summand. -/
theorem coneFinsetSum_ne_zero_of_mem
    {I : Type u} {J : Type v} [Finite I]
    (z : J → ConeVec I) (s : Finset J) (j : J) (hj : j ∈ s)
    (hz : z j ≠ 0) :
    (∑ k ∈ s, z k) ≠ 0 := by
  letI := Fintype.ofFinite I
  have hzMass : 0 < l1Mass (z j).1 := (coneNonzeroMass (z j)).mp hz
  apply (coneNonzeroMass (∑ k ∈ s, z k)).mpr
  have hle : l1Mass (z j).1 ≤ l1Mass (∑ k ∈ s, z k).1 := by
    unfold l1Mass
    apply Finset.sum_le_sum
    intro i _
    have happ : (∑ k ∈ s, z k).1 i = ∑ k ∈ s, (z k).1 i := by
      simp
    rw [happ]
    exact Finset.single_le_sum (fun k _ => (z k).2 i) hj
  exact hzMass.trans_le hle

private theorem qcvx_finsetSum_le
    {I : Type u} {J : Type v} [Finite I]
    (f : PosConeVec I → ℝ) (hscale : ScaleInvariant f) (hqcvx : QCvx f)
    (z : J → ConeVec I) (hz : ∀ j, z j ≠ 0)
    (M : ℝ) (hM : ∀ j, f (toPosCone (z j) (hz j)) ≤ M) :
    ∀ s : Finset J, ∀ hs : (∑ j ∈ s, z j) ≠ 0,
      f (toPosCone (∑ j ∈ s, z j) hs) ≤ M := by
  classical
  letI := Fintype.ofFinite I
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro hs
      exact (hs (by simp)).elim
  | @insert a s ha ih =>
      intro hs
      let r : ConeVec I := ∑ j ∈ s, z j
      have hsum : (∑ j ∈ insert a s, z j) = z a + r := by
        simp [r, ha]
      by_cases hr : r = 0
      · have heq : (∑ j ∈ insert a s, z j) = z a := by
          rw [hsum, hr, add_zero]
        have hpos : toPosCone (∑ j ∈ insert a s, z j) hs =
            toPosCone (z a) (hz a) := by
          apply Subtype.ext
          exact heq
        rw [hpos]
        exact hM a
      · have hadd := qcvx_coneAdd f hscale hqcvx (z a) r (hz a) hr
        have hpos : toPosCone (∑ j ∈ insert a s, z j) hs =
            toPosCone (z a + r) (by simpa [hsum] using hs) := by
          apply Subtype.ext
          exact hsum
        calc
          f (toPosCone (∑ j ∈ insert a s, z j) hs) =
              f (toPosCone (z a + r) (by simpa [hsum] using hs)) :=
            congrArg f hpos
          _ ≤ max (f (toPosCone (z a) (hz a)))
              (f (toPosCone r hr)) := hadd
          _ ≤ M := max_le (hM a) (by simpa [r] using ih hr)

private theorem maxQCave_finsetSum_ge
    {I : Type u} {J : Type v} [Finite I]
    (f : PosConeVec I → ℝ) (hscale : ScaleInvariant f)
    (hmax : MaxQCave f)
    (z : J → ConeVec I) (hz : ∀ j, z j ≠ 0) :
    ∀ s : Finset J, ∀ hs : (∑ j ∈ s, z j) ≠ 0,
      ∀ j ∈ s, f (toPosCone (z j) (hz j)) ≤
        f (toPosCone (∑ k ∈ s, z k) hs) := by
  classical
  letI := Fintype.ofFinite I
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      intro hs j hj
      let r : ConeVec I := ∑ k ∈ s, z k
      have hsum : (∑ k ∈ insert a s, z k) = z a + r := by
        simp [r, ha]
      have hpos : toPosCone (∑ k ∈ insert a s, z k) hs =
          toPosCone (z a + r) (by simpa [hsum] using hs) := by
        apply Subtype.ext
        exact hsum
      rcases Finset.mem_insert.mp hj with hja | hj
      · subst j
        by_cases hr : r = 0
        · have heq : (∑ k ∈ insert a s, z k) = z a := by
            rw [hsum, hr, add_zero]
          have heqPos : toPosCone (∑ k ∈ insert a s, z k) hs =
              toPosCone (z a) (hz a) := by
            apply Subtype.ext
            exact heq
          rw [heqPos]
        · have hadd := maxQCave_coneAdd f hscale hmax (z a) r (hz a) hr
          calc
            f (toPosCone (z a) (hz a)) ≤
                max (f (toPosCone (z a) (hz a)))
                  (f (toPosCone r hr)) := le_max_left _ _
            _ ≤ f (toPosCone (z a + r) (by simpa [hsum] using hs)) := hadd
            _ = f (toPosCone (∑ k ∈ insert a s, z k) hs) :=
              congrArg f hpos.symm
      · have hr : r ≠ 0 := by
          dsimp [r]
          exact coneFinsetSum_ne_zero_of_mem z s j hj (hz j)
        have hjr : f (toPosCone (z j) (hz j)) ≤ f (toPosCone r hr) := by
          simpa [r] using ih hr j hj
        have hadd := maxQCave_coneAdd f hscale hmax (z a) r (hz a) hr
        calc
          f (toPosCone (z j) (hz j)) ≤ f (toPosCone r hr) := hjr
          _ ≤ max (f (toPosCone (z a) (hz a)))
              (f (toPosCone r hr)) := le_max_right _ _
          _ ≤ f (toPosCone (z a + r) (by simpa [hsum] using hs)) := hadd
          _ = f (toPosCone (∑ k ∈ insert a s, z k) hs) :=
            congrArg f hpos.symm

/-! ## Exact finite quasi-mixing packages -/

/-- Finite quasi mixing for strictly positive coefficients and nonzero
summands. -/
theorem finiteQuasiMixing
    {I : Type u} {J : Type v}
    [Finite I] [Nonempty I] [Fintype J] [Nonempty J]
    (z : J → PosConeVec I) (c : J → ℝ) (hc : ∀ j, 0 < c j)
    (hs : weightedConeSum c (fun j => (hc j).le) (fun j => (z j).1) ≠ 0)
    (f : PosConeVec I → ℝ) :
    (ScaleInvariant f ∧ QCvx f →
      f (toPosCone
        (weightedConeSum c (fun j => (hc j).le) (fun j => (z j).1)) hs) ≤
        finMax fun j => f (z j)) ∧
    (ScaleInvariant f ∧ MaxQCave f →
      finMax (fun j => f (z j)) ≤
        f (toPosCone
          (weightedConeSum c (fun j => (hc j).le) (fun j => (z j).1)) hs)) := by
  classical
  let v : J → ConeVec I := fun j =>
    coneScale (c j) (hc j).le (z j).1
  have hzCone (j : J) : (z j).1 ≠ 0 := by
    intro hzero
    apply (z j).2
    exact congrArg Subtype.val hzero
  have hv (j : J) : v j ≠ 0 := by
    intro hzero
    apply hzCone j
    apply Subtype.ext
    funext i
    have hi := congrArg (fun q : ConeVec I => q.1 i) hzero
    have hprod : c j * (z j).1.1 i = 0 := by simpa [v, coneScale] using hi
    exact (mul_eq_zero.mp hprod).resolve_left (hc j).ne'
  have htoPos (j : J) : toPosCone (v j) (hv j) =
      posScale (c j) (hc j) (z j) := by
    rfl
  constructor
  · rintro ⟨hscale, hqcvx⟩
    have hM (j : J) : f (toPosCone (v j) (hv j)) ≤
        finMax (fun k => f (z k)) := by
      rw [htoPos j, hscale (z j) (c j) (hc j)]
      exact @le_finMax_apply J _ _ (fun k => f (z k)) j
    change f (toPosCone (coneSum v) hs) ≤ finMax (fun j => f (z j))
    exact qcvx_finsetSum_le f hscale hqcvx v hv _ hM Finset.univ (by
      simpa [v, weightedConeSum, coneSum] using hs)
  · rintro ⟨hscale, hmax⟩
    obtain ⟨j, hj⟩ := finMax_mem (fun j => f (z j))
    have hselected := maxQCave_finsetSum_ge f hscale hmax v hv Finset.univ (by
      simpa [v, weightedConeSum, coneSum] using hs) j (Finset.mem_univ j)
    rw [htoPos j, hscale (z j) (c j) (hc j)] at hselected
    change finMax (fun j => f (z j)) ≤ f (toPosCone (coneSum v) hs)
    rw [← hj]
    exact hselected

/-- Indices of strictly positive, nonzero weighted summands. -/
abbrev WeightedSupport
    {I : Type u} {J : Type v}
    (c : J → ℝ) (z : J → ConeVec I) :=
  {j : J // 0 < c j ∧ z j ≠ 0}

/-- A nonzero nonnegative weighted sum has a nonempty weighted support. -/
theorem weightedSupportNonempty
    {I : Type u} {J : Type v} [Fintype J]
    (z : J → ConeVec I) (c : J → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hs : weightedConeSum c hc z ≠ 0) :
    Nonempty (WeightedSupport c z) := by
  classical
  by_contra hnone
  apply hs
  apply Subtype.ext
  funext i
  change (coneSum fun j => coneScale (c j) (hc j) (z j)).1 i = 0
  rw [coneSum_apply]
  apply Finset.sum_eq_zero
  intro j _
  have hnot : ¬(0 < c j ∧ z j ≠ 0) := by
    intro hj
    exact hnone ⟨⟨j, hj⟩⟩
  by_cases hcpos : 0 < c j
  · have hz0 : z j = 0 := by
      by_contra hz
      exact hnot ⟨hcpos, hz⟩
    simp [coneScale, hz0]
  · have hc0 : c j = 0 := le_antisymm (not_lt.mp hcpos) (hc j)
    simp [coneScale, hc0]

/-- Deleting all zero weighted summands reduces the general finite
quasi-mixing rule to the strictly positive one. -/
theorem finiteQuasiMixing_deleteZero
    {I : Type u} {J : Type v}
    [Finite I] [Nonempty I] [Fintype J]
    (z : J → ConeVec I) (c : J → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hs : weightedConeSum c hc z ≠ 0)
    (f : PosConeVec I → ℝ) :
    let K := WeightedSupport c z
    letI : Finite K := Finite.of_injective Subtype.val Subtype.val_injective
    letI : Fintype K := Fintype.ofFinite K
    letI : Nonempty K := weightedSupportNonempty z c hc hs
    (ScaleInvariant f ∧ QCvx f →
      f (toPosCone (weightedConeSum c hc z) hs) ≤
        finMax (fun k : K => f (toPosCone (z k.1) k.2.2))) ∧
    (ScaleInvariant f ∧ MaxQCave f →
      finMax (fun k : K => f (toPosCone (z k.1) k.2.2)) ≤
        f (toPosCone (weightedConeSum c hc z) hs)) := by
  classical
  dsimp only
  let K := WeightedSupport c z
  letI : Finite K := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype K := Fintype.ofFinite K
  letI : Nonempty K := weightedSupportNonempty z c hc hs
  let zp : K → PosConeVec I := fun k => toPosCone (z k.1) k.2.2
  let cp : K → ℝ := fun k => c k.1
  have hcp (k : K) : 0 < cp k := k.2.1
  have hsum : weightedConeSum cp (fun k => (hcp k).le) (fun k => (zp k).1) =
      weightedConeSum c hc z := by
    apply Subtype.ext
    funext i
    change (coneSum fun k : K =>
      coneScale (cp k) (hcp k).le (zp k).1).1 i =
      (coneSum fun j : J => coneScale (c j) (hc j) (z j)).1 i
    rw [coneSum_apply, coneSum_apply]
    let s : Finset J := Finset.univ.filter fun j => 0 < c j ∧ z j ≠ 0
    calc
      (∑ k : K, (coneScale (cp k) (hcp k).le (zp k).1).1 i) =
          ∑ j ∈ s, (coneScale (c j) (hc j) (z j)).1 i := by
        exact (Finset.sum_subtype s (fun j => by simp [s])
          (fun j => (coneScale (c j) (hc j) (z j)).1 i)).symm
      _ = ∑ j : J, (coneScale (c j) (hc j) (z j)).1 i := by
        apply Finset.sum_subset (Finset.subset_univ s)
        intro j _ hj
        have hjnot : ¬(0 < c j ∧ z j ≠ 0) := by
          simpa [s] using hj
        by_cases hcpos : 0 < c j
        · have hz0 : z j = 0 := by
            by_contra hz
            exact hjnot ⟨hcpos, hz⟩
          simp [coneScale, hz0]
        · have hc0 : c j = 0 := le_antisymm (not_lt.mp hcpos) (hc j)
          simp [coneScale, hc0]
  have hsK : weightedConeSum cp (fun k => (hcp k).le)
      (fun k => (zp k).1) ≠ 0 := by
    rw [hsum]
    exact hs
  have hfinite := finiteQuasiMixing zp cp hcp hsK f
  have htoPosSum : toPosCone
      (weightedConeSum cp (fun k => (hcp k).le) (fun k => (zp k).1)) hsK =
      toPosCone (weightedConeSum c hc z) hs := by
    apply Subtype.ext
    exact hsum
  constructor
  · intro hshape
    have h := hfinite.1 hshape
    rw [htoPosSum] at h
    simpa [zp, K] using h
  · intro hshape
    have h := hfinite.2 hshape
    rw [htoPosSum] at h
    simpa [zp, K] using h

/-! ## Active-column extrema -/

theorem HMinus_le_active
    {X Y : Type u}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (τ : ProbabilityMeasure Param) (P : JointProb X Y) (y : Active P) :
    HMinus τ P ≤
      integratedEntropyPos (probMeasure τ) (conditional P y) := by
  classical
  letI : Fintype (Active P) :=
    Fintype.ofFinset (activeFinset P) fun _ => Iff.rfl
  letI : Nonempty (Active P) := activeNonempty P
  unfold HMinus
  exact finMin_le _ y

theorem le_HMinus_of_forall_active
    {X Y : Type u}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (τ : ProbabilityMeasure Param) (P : JointProb X Y) (r : ℝ)
    (h : ∀ y : Active P,
      r ≤ integratedEntropyPos (probMeasure τ) (conditional P y)) :
    r ≤ HMinus τ P := by
  classical
  letI : Fintype (Active P) :=
    Fintype.ofFinset (activeFinset P) fun _ => Iff.rfl
  letI : Nonempty (Active P) := activeNonempty P
  unfold HMinus
  obtain ⟨y, hy⟩ := finMin_mem
    (fun y : Active P =>
      integratedEntropyPos (probMeasure τ) (conditional P y))
  exact (h y).trans_eq hy

theorem active_le_HPlus
    {X Y : Type u}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (τ : ProbabilityMeasure Param) (P : JointProb X Y) (y : Active P) :
    integratedEntropyPos (probMeasure τ) (conditional P y) ≤ HPlus τ P := by
  classical
  letI : Fintype (Active P) :=
    Fintype.ofFinset (activeFinset P) fun _ => Iff.rfl
  letI : Nonempty (Active P) := activeNonempty P
  unfold HPlus
  exact @le_finMax_apply (Active P) _ _
    (fun y => integratedEntropyPos (probMeasure τ) (conditional P y)) y

theorem HPlus_le_of_forall_active
    {X Y : Type u}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (τ : ProbabilityMeasure Param) (P : JointProb X Y) (r : ℝ)
    (h : ∀ y : Active P,
      integratedEntropyPos (probMeasure τ) (conditional P y) ≤ r) :
    HPlus τ P ≤ r := by
  classical
  letI : Fintype (Active P) :=
    Fintype.ofFinset (activeFinset P) fun _ => Iff.rfl
  letI : Nonempty (Active P) := activeNonempty P
  unfold HPlus
  obtain ⟨y, hy⟩ := finMax_mem
    (fun y : Active P =>
      integratedEntropyPos (probMeasure τ) (conditional P y))
  exact hy.symm.trans_le (h y)

theorem exists_active_eq_HPlus
    {X Y : Type u}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (τ : ProbabilityMeasure Param) (P : JointProb X Y) :
    ∃ y : Active P,
      integratedEntropyPos (probMeasure τ) (conditional P y) = HPlus τ P := by
  classical
  letI : Fintype (Active P) :=
    Fintype.ofFinset (activeFinset P) fun _ => Iff.rfl
  letI : Nonempty (Active P) := activeNonempty P
  unfold HPlus
  exact finMax_mem _

theorem aTrop_activeColumn
    {X : Type u} {Y : Type v}
    [Fintype X] [Nonempty X] [Fintype Y]
    (τ : ProbabilityMeasure Param) (P : JointProb X Y) (y : Active P) :
    aTrop τ (toPosCone (column P y.1) (active_column_ne_zero P y)) =
      integratedEntropyPos (probMeasure τ) (conditional P y) := rfl

theorem gTrop_activeColumn
    {X : Type u} {Y : Type v}
    [Fintype X] [Nonempty X] [Fintype Y]
    (τ : ProbabilityMeasure Param) (P : JointProb X Y) (y : Active P) :
    gTrop τ (toPosCone (column P y.1) (active_column_ne_zero P y)) =
      -integratedEntropyPos (probMeasure τ) (conditional P y) := rfl

/-! ## Forward tropical channel reductions -/

/-- Quasi-convexity of the negative tropical column function implies
fixed-row monotonicity of the minimum candidate. -/
theorem cmMonotoneAtRow_HMinus_of_qcvx
    (X : Type u) [Fintype X] [Nonempty X]
    (τ : ProbabilityMeasure Param)
    (hqcvx : QCvx (gTrop τ : PosConeVec X → ℝ)) :
    CMMonotoneAtRow X (HMinus τ) := by
  classical
  intro Y Y' _ _ _ _ P Q hPQ
  rcases (cmRel_iff_eq_output P Q).mp hPQ with ⟨C, rfl⟩
  apply le_HMinus_of_forall_active τ (cmOutput C P) (HMinus τ P)
  intro yq
  let z : Fin C.n × Y → ConeVec X := fun ky =>
    coneMatrixAction (C.S ky.1) (C.hS ky.1).1 (column P ky.2)
  let c : Fin C.n × Y → ℝ := fun ky => C.D ky.1 ky.2 yq.1
  have hc (ky : Fin C.n × Y) : 0 ≤ c ky := C.hD ky.1 ky.2 yq.1
  have hsumEq : weightedConeSum c hc z =
      column (cmOutput C P) yq.1 := by
    simpa [weightedConeSum, z, c] using
      (cmOutput_column_decomposition C P yq.1).symm
  have hsum : weightedConeSum c hc z ≠ 0 := by
    rw [hsumEq]
    exact active_column_ne_zero (cmOutput C P) yq
  let K := WeightedSupport c z
  letI : Finite K := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype K := Fintype.ofFinite K
  letI : Nonempty K := weightedSupportNonempty z c hc hsum
  have hmix := (finiteQuasiMixing_deleteZero z c hc hsum
    (gTrop τ : PosConeVec X → ℝ)).1
    ⟨gTrop_scaleInvariant τ, hqcvx⟩
  have hbound (k : K) :
      gTrop τ (toPosCone (z k.1) k.2.2) ≤ -HMinus τ P := by
    have hmassAction : 0 < l1Mass (z k.1).1 :=
      (coneNonzeroMass (z k.1)).mp k.2.2
    have hmassInput : 0 < l1Mass (column P k.1.2).1 := by
      rw [show l1Mass (z k.1).1 = l1Mass (column P k.1.2).1 by
        dsimp [z]
        exact doublyStochastic_mass (C.S k.1.1) (C.hS k.1.1)
          (column P k.1.2)] at hmassAction
      exact hmassAction
    have hinput : column P k.1.2 ≠ 0 :=
      (coneNonzeroMass (column P k.1.2)).mpr hmassInput
    let yp : Active P := ⟨k.1.2, by
      rw [activeFinset, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hmassInput⟩⟩
    have hschur : gTrop τ (toPosCone (z k.1) k.2.2) ≤
        gTrop τ (toPosCone (column P k.1.2) hinput) := by
      have heq : posConeMatrixAction (C.S k.1.1) (C.hS k.1.1)
          (toPosCone (column P k.1.2) hinput) =
          toPosCone (z k.1) k.2.2 := by
        apply Subtype.ext
        rfl
      rw [← heq]
      exact gTrop_posConeMatrixAction_le τ (C.S k.1.1) (C.hS k.1.1)
        (toPosCone (column P k.1.2) hinput)
    calc
      gTrop τ (toPosCone (z k.1) k.2.2) ≤
          gTrop τ (toPosCone (column P k.1.2) hinput) := hschur
      _ = -integratedEntropyPos (probMeasure τ) (conditional P yp) := by
        exact gTrop_activeColumn τ P yp
      _ ≤ -HMinus τ P := neg_le_neg (HMinus_le_active τ P yp)
  have hmaxBound : finMax (fun k : K =>
      gTrop τ (toPosCone (z k.1) k.2.2)) ≤ -HMinus τ P := by
    obtain ⟨k, hk⟩ := finMax_mem
      (fun k : K => gTrop τ (toPosCone (z k.1) k.2.2))
    exact hk.symm.trans_le (hbound k)
  have hq : gTrop τ (toPosCone
      (column (cmOutput C P) yq.1)
      (active_column_ne_zero (cmOutput C P) yq)) ≤ -HMinus τ P := by
    have htoPos : toPosCone (weightedConeSum c hc z) hsum =
        toPosCone (column (cmOutput C P) yq.1)
          (active_column_ne_zero (cmOutput C P) yq) := by
      apply Subtype.ext
      exact hsumEq
    rw [← htoPos]
    exact hmix.trans hmaxBound
  rw [gTrop_activeColumn τ (cmOutput C P) yq] at hq
  linarith

/-- Max-quasi-concavity of the positive tropical column function implies
fixed-row monotonicity of the maximum candidate. -/
theorem cmMonotoneAtRow_HPlus_of_maxQCave
    (X : Type u) [Fintype X] [Nonempty X]
    (τ : ProbabilityMeasure Param)
    (hmax : MaxQCave (aTrop τ : PosConeVec X → ℝ)) :
    CMMonotoneAtRow X (HPlus τ) := by
  classical
  intro Y Y' _ _ _ _ P Q hPQ
  rcases (cmRel_iff_eq_output P Q).mp hPQ with ⟨C, rfl⟩
  obtain ⟨y0, hy0⟩ := exists_active_eq_HPlus τ P
  have hDsum : (∑ ky : Fin C.n × Y', C.D ky.1 y0.1 ky.2) = 1 := by
    rw [Fintype.sum_prod_type]
    exact C.hnorm y0.1
  have hDsum_ne : (∑ ky : Fin C.n × Y', C.D ky.1 y0.1 ky.2) ≠ 0 := by
    rw [hDsum]
    norm_num
  obtain ⟨ky, _hky, hDne⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hDsum_ne
  have hDpos : 0 < C.D ky.1 y0.1 ky.2 :=
    lt_of_le_of_ne (C.hD ky.1 y0.1 ky.2) (Ne.symm hDne)
  let z : Fin C.n × Y → ConeVec X := fun jy =>
    coneMatrixAction (C.S jy.1) (C.hS jy.1).1 (column P jy.2)
  let c : Fin C.n × Y → ℝ := fun jy => C.D jy.1 jy.2 ky.2
  have hc (jy : Fin C.n × Y) : 0 ≤ c jy := C.hD jy.1 jy.2 ky.2
  let j0 : Fin C.n × Y := (ky.1, y0.1)
  have hinput : column P y0.1 ≠ 0 := active_column_ne_zero P y0
  have hz0 : z j0 ≠ 0 := by
    dsimp [z, j0]
    exact coneMatrixAction_ne_zero (C.S ky.1) (C.hS ky.1)
      (column P y0.1) hinput
  have hc0 : 0 < c j0 := by simpa [c, j0] using hDpos
  let v : Fin C.n × Y → ConeVec X := fun j => coneScale (c j) (hc j) (z j)
  have hv0 : v j0 ≠ 0 := by
    intro hzero
    apply hz0
    apply Subtype.ext
    funext i
    have hi := congrArg (fun q : ConeVec X => q.1 i) hzero
    have hprod : c j0 * (z j0).1 i = 0 := by simpa [v, coneScale] using hi
    exact (mul_eq_zero.mp hprod).resolve_left hc0.ne'
  have hsum : weightedConeSum c hc z ≠ 0 := by
    change coneSum v ≠ 0
    exact coneFinsetSum_ne_zero_of_mem v Finset.univ j0
      (Finset.mem_univ j0) hv0
  have hsumEq : weightedConeSum c hc z =
      column (cmOutput C P) ky.2 := by
    simpa [weightedConeSum, z, c] using
      (cmOutput_column_decomposition C P ky.2).symm
  have hout : column (cmOutput C P) ky.2 ≠ 0 := by
    rw [← hsumEq]
    exact hsum
  let yq : Active (cmOutput C P) := ⟨ky.2, by
    rw [activeFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (coneNonzeroMass _).mp hout⟩⟩
  let K := WeightedSupport c z
  letI : Finite K := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype K := Fintype.ofFinite K
  letI : Nonempty K := weightedSupportNonempty z c hc hsum
  let k0 : K := ⟨j0, hc0, hz0⟩
  have hmix := (finiteQuasiMixing_deleteZero z c hc hsum
    (aTrop τ : PosConeVec X → ℝ)).2
    ⟨aTrop_scaleInvariant τ, hmax⟩
  have hselected : aTrop τ (toPosCone (z j0) hz0) ≤
      finMax (fun k : K => aTrop τ (toPosCone (z k.1) k.2.2)) := by
    have hk := @le_finMax_apply K _ _
      (fun k : K => aTrop τ (toPosCone (z k.1) k.2.2)) k0
    simpa [k0] using hk
  have hschur : integratedEntropyPos (probMeasure τ) (conditional P y0) ≤
      aTrop τ (toPosCone (z j0) hz0) := by
    have heq : posConeMatrixAction (C.S ky.1) (C.hS ky.1)
        (toPosCone (column P y0.1) hinput) =
        toPosCone (z j0) hz0 := by
      apply Subtype.ext
      rfl
    rw [← aTrop_activeColumn τ P y0, ← heq]
    exact aTrop_posConeMatrixAction_ge τ (C.S ky.1) (C.hS ky.1)
      (toPosCone (column P y0.1) hinput)
  have htoPos : toPosCone (weightedConeSum c hc z) hsum =
      toPosCone (column (cmOutput C P) ky.2) hout := by
    apply Subtype.ext
    exact hsumEq
  have houtput : finMax (fun k : K =>
      aTrop τ (toPosCone (z k.1) k.2.2)) ≤
      integratedEntropyPos (probMeasure τ) (conditional (cmOutput C P) yq) := by
    rw [← aTrop_activeColumn τ (cmOutput C P) yq, ← htoPos]
    exact hmix
  calc
    HPlus τ P = integratedEntropyPos (probMeasure τ) (conditional P y0) :=
      hy0.symm
    _ ≤ aTrop τ (toPosCone (z j0) hz0) := hschur
    _ ≤ finMax (fun k : K => aTrop τ (toPosCone (z k.1) k.2.2)) :=
      hselected
    _ ≤ integratedEntropyPos (probMeasure τ)
        (conditional (cmOutput C P) yq) := houtput
    _ ≤ HPlus τ (cmOutput C P) := active_le_HPlus τ _ yq

/-! ## The tropical two-column merge -/

theorem coneScale_ne_zero_of_pos
    {I : Type u} (c : ℝ) (hc : 0 < c) (x : ConeVec I) (hx : x ≠ 0) :
    coneScale c hc.le x ≠ 0 := by
  intro hzero
  apply hx
  apply Subtype.ext
  funext i
  have hi := congrArg (fun q : ConeVec I => q.1 i) hzero
  have hprod : c * x.1 i = 0 := by simpa [coneScale] using hi
  exact (mul_eq_zero.mp hprod).resolve_left hc.ne'

def normalizedTwoColumnActiveZero
    {I : Type u} [Fintype I]
    (x z : PosConeVec I) (lambda : ℝ)
    (hlambda : 0 < lambda ∧ lambda < 1)
    (hm : 0 < l1Mass
      (coneMix lambda ⟨hlambda.1.le, hlambda.2.le⟩ x.1 z.1).1) :
    Active (normalizedTwoColumn x.1 z.1 lambda
      ⟨hlambda.1.le, hlambda.2.le⟩ hm) := by
  let hclosed : lambda ∈ Icc (0 : ℝ) 1 :=
    ⟨hlambda.1.le, hlambda.2.le⟩
  let P := normalizedTwoColumn x.1 z.1 lambda hclosed hm
  have hx : x.1 ≠ 0 := by
    intro hzero
    apply x.2
    exact congrArg Subtype.val hzero
  have hc : 0 < lambda / l1Mass (coneMix lambda hclosed x.1 z.1).1 :=
    div_pos hlambda.1 hm
  have hcol : column P (ULift.up (0 : Fin 2)) ≠ 0 := by
    rw [normalizedTwoColumn_column_zero]
    exact coneScale_ne_zero_of_pos _ hc x.1 hx
  exact ⟨ULift.up (0 : Fin 2), by
    rw [activeFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (coneNonzeroMass _).mp hcol⟩⟩

def normalizedTwoColumnActiveOne
    {I : Type u} [Fintype I]
    (x z : PosConeVec I) (lambda : ℝ)
    (hlambda : 0 < lambda ∧ lambda < 1)
    (hm : 0 < l1Mass
      (coneMix lambda ⟨hlambda.1.le, hlambda.2.le⟩ x.1 z.1).1) :
    Active (normalizedTwoColumn x.1 z.1 lambda
      ⟨hlambda.1.le, hlambda.2.le⟩ hm) := by
  let hclosed : lambda ∈ Icc (0 : ℝ) 1 :=
    ⟨hlambda.1.le, hlambda.2.le⟩
  let P := normalizedTwoColumn x.1 z.1 lambda hclosed hm
  have hz : z.1 ≠ 0 := by
    intro hzero
    apply z.2
    exact congrArg Subtype.val hzero
  have hc : 0 < (1 - lambda) /
      l1Mass (coneMix lambda hclosed x.1 z.1).1 :=
    div_pos (sub_pos.mpr hlambda.2) hm
  have hcol : column P (ULift.up (1 : Fin 2)) ≠ 0 := by
    rw [normalizedTwoColumn_column_one]
    exact coneScale_ne_zero_of_pos _ hc z.1 hz
  exact ⟨ULift.up (1 : Fin 2), by
    rw [activeFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (coneNonzeroMass _).mp hcol⟩⟩

@[simp] theorem normalizedTwoColumn_conditional_zero
    {I : Type u} [Fintype I] [Nonempty I]
    (x z : PosConeVec I) (lambda : ℝ)
    (hlambda : 0 < lambda ∧ lambda < 1)
    (hm : 0 < l1Mass
      (coneMix lambda ⟨hlambda.1.le, hlambda.2.le⟩ x.1 z.1).1) :
    conditional
      (normalizedTwoColumn x.1 z.1 lambda
        ⟨hlambda.1.le, hlambda.2.le⟩ hm)
      (normalizedTwoColumnActiveZero x z lambda hlambda hm) =
      normalize x := by
  let hclosed : lambda ∈ Icc (0 : ℝ) 1 :=
    ⟨hlambda.1.le, hlambda.2.le⟩
  have hc : 0 < lambda / l1Mass (coneMix lambda hclosed x.1 z.1).1 :=
    div_pos hlambda.1 hm
  have hpos : toPosCone
      (column (normalizedTwoColumn x.1 z.1 lambda hclosed hm)
        (normalizedTwoColumnActiveZero x z lambda hlambda hm).1)
      (active_column_ne_zero _
        (normalizedTwoColumnActiveZero x z lambda hlambda hm)) =
      posScale (lambda / l1Mass (coneMix lambda hclosed x.1 z.1).1)
        hc x := by
    apply Subtype.ext
    change column (normalizedTwoColumn x.1 z.1 lambda hclosed hm)
      (normalizedTwoColumnActiveZero x z lambda hlambda hm).1 =
      coneScale (lambda / l1Mass (coneMix lambda hclosed x.1 z.1).1)
        hc.le x.1
    simpa [normalizedTwoColumnActiveZero] using
      normalizedTwoColumn_column_zero x.1 z.1 lambda hclosed hm
  unfold conditional
  rw [hpos, normalize_posScale]

@[simp] theorem normalizedTwoColumn_conditional_one
    {I : Type u} [Fintype I] [Nonempty I]
    (x z : PosConeVec I) (lambda : ℝ)
    (hlambda : 0 < lambda ∧ lambda < 1)
    (hm : 0 < l1Mass
      (coneMix lambda ⟨hlambda.1.le, hlambda.2.le⟩ x.1 z.1).1) :
    conditional
      (normalizedTwoColumn x.1 z.1 lambda
        ⟨hlambda.1.le, hlambda.2.le⟩ hm)
      (normalizedTwoColumnActiveOne x z lambda hlambda hm) =
      normalize z := by
  let hclosed : lambda ∈ Icc (0 : ℝ) 1 :=
    ⟨hlambda.1.le, hlambda.2.le⟩
  have hc : 0 < (1 - lambda) /
      l1Mass (coneMix lambda hclosed x.1 z.1).1 :=
    div_pos (sub_pos.mpr hlambda.2) hm
  have hpos : toPosCone
      (column (normalizedTwoColumn x.1 z.1 lambda hclosed hm)
        (normalizedTwoColumnActiveOne x z lambda hlambda hm).1)
      (active_column_ne_zero _
        (normalizedTwoColumnActiveOne x z lambda hlambda hm)) =
      posScale ((1 - lambda) /
        l1Mass (coneMix lambda hclosed x.1 z.1).1) hc z := by
    apply Subtype.ext
    change column (normalizedTwoColumn x.1 z.1 lambda hclosed hm)
      (normalizedTwoColumnActiveOne x z lambda hlambda hm).1 =
      coneScale ((1 - lambda) /
        l1Mass (coneMix lambda hclosed x.1 z.1).1) hc.le z.1
    simpa [normalizedTwoColumnActiveOne] using
      normalizedTwoColumn_column_one x.1 z.1 lambda hclosed hm
  unfold conditional
  rw [hpos, normalize_posScale]

def mergeTwoChannelActive
    {I : Type u} [Fintype I]
    (x z : PosConeVec I) (lambda : ℝ)
    (hlambda : 0 < lambda ∧ lambda < 1)
    (hm : 0 < l1Mass
      (coneMix lambda ⟨hlambda.1.le, hlambda.2.le⟩ x.1 z.1).1) :
    Active (cmOutput (mergeTwoChannel I)
      (normalizedTwoColumn x.1 z.1 lambda
        ⟨hlambda.1.le, hlambda.2.le⟩ hm)) := by
  let hclosed : lambda ∈ Icc (0 : ℝ) 1 :=
    ⟨hlambda.1.le, hlambda.2.le⟩
  let P := normalizedTwoColumn x.1 z.1 lambda hclosed hm
  let Q := cmOutput (mergeTwoChannel I) P
  have hmix : coneMix lambda hclosed x.1 z.1 ≠ 0 :=
    (coneNonzeroMass _).mpr hm
  have hc : 0 < 1 / l1Mass (coneMix lambda hclosed x.1 z.1).1 :=
    one_div_pos.mpr hm
  have hcol : column Q (ULift.up ()) ≠ 0 := by
    rw [mergeTwoChannel_output_column]
    exact coneScale_ne_zero_of_pos _ hc _ hmix
  exact ⟨ULift.up (), by
    rw [activeFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (coneNonzeroMass _).mp hcol⟩⟩

@[simp] theorem mergeTwoChannel_conditional
    {I : Type u} [Fintype I] [Nonempty I]
    (x z : PosConeVec I) (lambda : ℝ)
    (hlambda : 0 < lambda ∧ lambda < 1)
    (hm : 0 < l1Mass
      (coneMix lambda ⟨hlambda.1.le, hlambda.2.le⟩ x.1 z.1).1) :
    conditional
      (cmOutput (mergeTwoChannel I)
        (normalizedTwoColumn x.1 z.1 lambda
          ⟨hlambda.1.le, hlambda.2.le⟩ hm))
      (mergeTwoChannelActive x z lambda hlambda hm) =
      normalize (posMix lambda hlambda x z) := by
  let hclosed : lambda ∈ Icc (0 : ℝ) 1 :=
    ⟨hlambda.1.le, hlambda.2.le⟩
  have hc : 0 < 1 / l1Mass (coneMix lambda hclosed x.1 z.1).1 :=
    one_div_pos.mpr hm
  have hpos : toPosCone
      (column (cmOutput (mergeTwoChannel I)
        (normalizedTwoColumn x.1 z.1 lambda hclosed hm))
        (mergeTwoChannelActive x z lambda hlambda hm).1)
      (active_column_ne_zero _
        (mergeTwoChannelActive x z lambda hlambda hm)) =
      posScale (1 / l1Mass (coneMix lambda hclosed x.1 z.1).1) hc
        (posMix lambda hlambda x z) := by
    apply Subtype.ext
    change column (cmOutput (mergeTwoChannel I)
      (normalizedTwoColumn x.1 z.1 lambda hclosed hm))
      (mergeTwoChannelActive x z lambda hlambda hm).1 =
      coneScale (1 / l1Mass (coneMix lambda hclosed x.1 z.1).1) hc.le
        (coneMix lambda hclosed x.1 z.1)
    simpa [mergeTwoChannelActive] using
      mergeTwoChannel_output_column x.1 z.1 lambda hclosed hm
  unfold conditional
  rw [hpos, normalize_posScale]

theorem normalizedTwoColumn_active_cases
    {I : Type u} [Fintype I]
    (x z : PosConeVec I) (lambda : ℝ)
    (hlambda : 0 < lambda ∧ lambda < 1)
    (hm : 0 < l1Mass
      (coneMix lambda ⟨hlambda.1.le, hlambda.2.le⟩ x.1 z.1).1)
    (y : Active (normalizedTwoColumn x.1 z.1 lambda
      ⟨hlambda.1.le, hlambda.2.le⟩ hm)) :
    y = normalizedTwoColumnActiveZero x z lambda hlambda hm ∨
      y = normalizedTwoColumnActiveOne x z lambda hlambda hm := by
  rcases y with ⟨⟨j⟩, hy⟩
  fin_cases j
  · left
    apply Subtype.ext
    rfl
  · right
    apply Subtype.ext
    rfl

theorem HMinus_normalizedTwoColumn
    {I : Type u} [Fintype I] [Nonempty I]
    (τ : ProbabilityMeasure Param)
    (x z : PosConeVec I) (lambda : ℝ)
    (hlambda : 0 < lambda ∧ lambda < 1)
    (hm : 0 < l1Mass
      (coneMix lambda ⟨hlambda.1.le, hlambda.2.le⟩ x.1 z.1).1) :
    HMinus τ (normalizedTwoColumn x.1 z.1 lambda
      ⟨hlambda.1.le, hlambda.2.le⟩ hm) =
      min (aTrop τ x) (aTrop τ z) := by
  let P := normalizedTwoColumn x.1 z.1 lambda
    ⟨hlambda.1.le, hlambda.2.le⟩ hm
  let y0 := normalizedTwoColumnActiveZero x z lambda hlambda hm
  let y1 := normalizedTwoColumnActiveOne x z lambda hlambda hm
  apply le_antisymm
  · apply le_min
    · calc
        HMinus τ P ≤ integratedEntropyPos (probMeasure τ)
            (conditional P y0) := HMinus_le_active τ P y0
        _ = aTrop τ x := by
          rw [normalizedTwoColumn_conditional_zero]
          rfl
    · calc
        HMinus τ P ≤ integratedEntropyPos (probMeasure τ)
            (conditional P y1) := HMinus_le_active τ P y1
        _ = aTrop τ z := by
          rw [normalizedTwoColumn_conditional_one]
          rfl
  · apply le_HMinus_of_forall_active τ P
    intro y
    rcases normalizedTwoColumn_active_cases x z lambda hlambda hm y with
      rfl | rfl
    · rw [normalizedTwoColumn_conditional_zero]
      exact min_le_left _ _
    · rw [normalizedTwoColumn_conditional_one]
      exact min_le_right _ _

theorem HPlus_normalizedTwoColumn
    {I : Type u} [Fintype I] [Nonempty I]
    (τ : ProbabilityMeasure Param)
    (x z : PosConeVec I) (lambda : ℝ)
    (hlambda : 0 < lambda ∧ lambda < 1)
    (hm : 0 < l1Mass
      (coneMix lambda ⟨hlambda.1.le, hlambda.2.le⟩ x.1 z.1).1) :
    HPlus τ (normalizedTwoColumn x.1 z.1 lambda
      ⟨hlambda.1.le, hlambda.2.le⟩ hm) =
      max (aTrop τ x) (aTrop τ z) := by
  let P := normalizedTwoColumn x.1 z.1 lambda
    ⟨hlambda.1.le, hlambda.2.le⟩ hm
  let y0 := normalizedTwoColumnActiveZero x z lambda hlambda hm
  let y1 := normalizedTwoColumnActiveOne x z lambda hlambda hm
  apply le_antisymm
  · apply HPlus_le_of_forall_active τ P
    intro y
    rcases normalizedTwoColumn_active_cases x z lambda hlambda hm y with
      rfl | rfl
    · rw [normalizedTwoColumn_conditional_zero]
      exact le_max_left _ _
    · rw [normalizedTwoColumn_conditional_one]
      exact le_max_right _ _
  · apply max_le
    · calc
        aTrop τ x = integratedEntropyPos (probMeasure τ)
            (conditional P y0) := by
          rw [normalizedTwoColumn_conditional_zero]
          rfl
        _ ≤ HPlus τ P := active_le_HPlus τ P y0
    · calc
        aTrop τ z = integratedEntropyPos (probMeasure τ)
            (conditional P y1) := by
          rw [normalizedTwoColumn_conditional_one]
          rfl
        _ ≤ HPlus τ P := active_le_HPlus τ P y1

theorem mergeTwoChannel_active_eq
    {I : Type u} [Fintype I]
    (x z : PosConeVec I) (lambda : ℝ)
    (hlambda : 0 < lambda ∧ lambda < 1)
    (hm : 0 < l1Mass
      (coneMix lambda ⟨hlambda.1.le, hlambda.2.le⟩ x.1 z.1).1)
    (y : Active (cmOutput (mergeTwoChannel I)
      (normalizedTwoColumn x.1 z.1 lambda
        ⟨hlambda.1.le, hlambda.2.le⟩ hm))) :
    y = mergeTwoChannelActive x z lambda hlambda hm := by
  rcases y with ⟨⟨j⟩, hy⟩
  rcases j with ⟨⟩
  apply Subtype.ext
  rfl

theorem HMinus_mergeTwoChannel
    {I : Type u} [Fintype I] [Nonempty I]
    (τ : ProbabilityMeasure Param)
    (x z : PosConeVec I) (lambda : ℝ)
    (hlambda : 0 < lambda ∧ lambda < 1)
    (hm : 0 < l1Mass
      (coneMix lambda ⟨hlambda.1.le, hlambda.2.le⟩ x.1 z.1).1) :
    HMinus τ (cmOutput (mergeTwoChannel I)
      (normalizedTwoColumn x.1 z.1 lambda
        ⟨hlambda.1.le, hlambda.2.le⟩ hm)) =
      aTrop τ (posMix lambda hlambda x z) := by
  let Q := cmOutput (mergeTwoChannel I)
    (normalizedTwoColumn x.1 z.1 lambda
      ⟨hlambda.1.le, hlambda.2.le⟩ hm)
  let yq := mergeTwoChannelActive x z lambda hlambda hm
  apply le_antisymm
  · calc
      HMinus τ Q ≤ integratedEntropyPos (probMeasure τ)
          (conditional Q yq) := HMinus_le_active τ Q yq
      _ = aTrop τ (posMix lambda hlambda x z) := by
        rw [mergeTwoChannel_conditional]
        rfl
  · apply le_HMinus_of_forall_active τ Q
    intro y
    rw [mergeTwoChannel_active_eq x z lambda hlambda hm y,
      mergeTwoChannel_conditional]
    rfl

theorem HPlus_mergeTwoChannel
    {I : Type u} [Fintype I] [Nonempty I]
    (τ : ProbabilityMeasure Param)
    (x z : PosConeVec I) (lambda : ℝ)
    (hlambda : 0 < lambda ∧ lambda < 1)
    (hm : 0 < l1Mass
      (coneMix lambda ⟨hlambda.1.le, hlambda.2.le⟩ x.1 z.1).1) :
    HPlus τ (cmOutput (mergeTwoChannel I)
      (normalizedTwoColumn x.1 z.1 lambda
        ⟨hlambda.1.le, hlambda.2.le⟩ hm)) =
      aTrop τ (posMix lambda hlambda x z) := by
  let Q := cmOutput (mergeTwoChannel I)
    (normalizedTwoColumn x.1 z.1 lambda
      ⟨hlambda.1.le, hlambda.2.le⟩ hm)
  let yq := mergeTwoChannelActive x z lambda hlambda hm
  apply le_antisymm
  · apply HPlus_le_of_forall_active τ Q
    intro y
    rw [mergeTwoChannel_active_eq x z lambda hlambda hm y,
      mergeTwoChannel_conditional]
    rfl
  · calc
      aTrop τ (posMix lambda hlambda x z) =
          integratedEntropyPos (probMeasure τ) (conditional Q yq) := by
        rw [mergeTwoChannel_conditional]
        rfl
      _ ≤ HPlus τ Q := active_le_HPlus τ Q yq

/-! ## Converse and exact tropical reductions -/

/-- Fixed-row monotonicity of the minimum candidate forces quasi-convexity
of the negative tropical column function. -/
theorem qcvx_gTrop_of_cmMonotoneAtRow
    (X : Type u) [Fintype X] [Nonempty X]
    (τ : ProbabilityMeasure Param)
    (hmono : CMMonotoneAtRow X (HMinus τ)) :
    QCvx (gTrop τ : PosConeVec X → ℝ) := by
  intro x z lambda hlambda
  let hclosed : lambda ∈ Icc (0 : ℝ) 1 :=
    ⟨hlambda.1.le, hlambda.2.le⟩
  have hmix : coneMix lambda hclosed x.1 z.1 ≠ 0 := by
    intro hzero
    apply (posMix lambda hlambda x z).2
    exact congrArg Subtype.val hzero
  have hm : 0 < l1Mass (coneMix lambda hclosed x.1 z.1).1 :=
    (coneNonzeroMass _).mp hmix
  let P := normalizedTwoColumn x.1 z.1 lambda hclosed hm
  let Q := cmOutput (mergeTwoChannel X) P
  have hrel : CMRel P Q := ⟨mergeTwoChannel X, fun _ _ => rfl⟩
  have hH : HMinus τ P ≤ HMinus τ Q :=
    @hmono (ULift.{u} (Fin 2)) (ULift.{u} Unit)
      inferInstance inferInstance inferInstance inferInstance P Q hrel
  rw [HMinus_normalizedTwoColumn τ x z lambda hlambda hm,
    HMinus_mergeTwoChannel τ x z lambda hlambda hm] at hH
  unfold gTrop
  by_cases hxz : aTrop τ x ≤ aTrop τ z
  · rw [min_eq_left hxz] at hH
    rw [max_eq_left (neg_le_neg hxz)]
    exact neg_le_neg hH
  · have hzx : aTrop τ z ≤ aTrop τ x := le_of_not_ge hxz
    rw [min_eq_right hzx] at hH
    rw [max_eq_right (neg_le_neg hzx)]
    exact neg_le_neg hH

/-- Fixed-row monotonicity of the maximum candidate forces
max-quasi-concavity of the positive tropical column function. -/
theorem maxQCave_aTrop_of_cmMonotoneAtRow
    (X : Type u) [Fintype X] [Nonempty X]
    (τ : ProbabilityMeasure Param)
    (hmono : CMMonotoneAtRow X (HPlus τ)) :
    MaxQCave (aTrop τ : PosConeVec X → ℝ) := by
  intro x z lambda hlambda
  let hclosed : lambda ∈ Icc (0 : ℝ) 1 :=
    ⟨hlambda.1.le, hlambda.2.le⟩
  have hmix : coneMix lambda hclosed x.1 z.1 ≠ 0 := by
    intro hzero
    apply (posMix lambda hlambda x z).2
    exact congrArg Subtype.val hzero
  have hm : 0 < l1Mass (coneMix lambda hclosed x.1 z.1).1 :=
    (coneNonzeroMass _).mp hmix
  let P := normalizedTwoColumn x.1 z.1 lambda hclosed hm
  let Q := cmOutput (mergeTwoChannel X) P
  have hrel : CMRel P Q := ⟨mergeTwoChannel X, fun _ _ => rfl⟩
  have hH : HPlus τ P ≤ HPlus τ Q :=
    @hmono (ULift.{u} (Fin 2)) (ULift.{u} Unit)
      inferInstance inferInstance inferInstance inferInstance P Q hrel
  rw [HPlus_normalizedTwoColumn τ x z lambda hlambda hm,
    HPlus_mergeTwoChannel τ x z lambda hlambda hm] at hH
  exact hH

/-- Exact fixed-row tropical shape reduction. -/
theorem tropicalShapeReduction
    (X : Type u) [Fintype X] [Nonempty X]
    (τ : ProbabilityMeasure Param) :
    (CMMonotoneAtRow X (HMinus τ) ↔
      QCvx (gTrop τ : PosConeVec X → ℝ)) ∧
    (CMMonotoneAtRow X (HPlus τ) ↔
      MaxQCave (aTrop τ : PosConeVec X → ℝ)) := by
  constructor
  · exact ⟨qcvx_gTrop_of_cmMonotoneAtRow X τ,
      cmMonotoneAtRow_HMinus_of_qcvx X τ⟩
  · exact ⟨maxQCave_aTrop_of_cmMonotoneAtRow X τ,
      cmMonotoneAtRow_HPlus_of_maxQCave X τ⟩

/-- Exact global tropical shape reduction. -/
theorem globalTropicalShapeReduction
    (τ : ProbabilityMeasure Param) :
    (CMMonotone (HMinus τ : PolyJointFunctional.{u}) ↔
      ∀ {X : Type u} [Fintype X] [Nonempty X],
        QCvx (gTrop τ : PosConeVec X → ℝ)) ∧
    (CMMonotone (HPlus τ : PolyJointFunctional.{u}) ↔
      ∀ {X : Type u} [Fintype X] [Nonempty X],
        MaxQCave (aTrop τ : PosConeVec X → ℝ)) := by
  constructor
  · constructor
    · intro hmono X _ _
      apply qcvx_gTrop_of_cmMonotoneAtRow X τ
      intro Y Y' _ _ _ _ P Q hPQ
      exact hmono P Q hPQ
    · intro hshape X Y Y' _ _ _ _ _ _ P Q hPQ
      exact cmMonotoneAtRow_HMinus_of_qcvx X τ hshape P Q hPQ
  · constructor
    · intro hmono X _ _
      apply maxQCave_aTrop_of_cmMonotoneAtRow X τ
      intro Y Y' _ _ _ _ P Q hPQ
      exact hmono P Q hPQ
    · intro hshape X Y Y' _ _ _ _ _ _ P Q hPQ
      exact cmMonotoneAtRow_HPlus_of_maxQCave X τ hshape P Q hPQ

end ConditionalEntropy
