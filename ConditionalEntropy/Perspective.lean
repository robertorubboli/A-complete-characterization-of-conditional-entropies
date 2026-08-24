import ConditionalEntropy.ColumnFunctions

/-!
# Total simplex perspectives

The perspective is defined on the complete nonnegative cone, with an explicit
zero branch.  Concavity is proved directly from simplex concavity and the
mass-weighted normalization identity.
-/

noncomputable section

open Set

namespace ConditionalEntropy

universe u

def perspective {I : Type u} [Fintype I] [Nonempty I]
    (f : ProbVec I → ℝ) (x : ConeVec I) : ℝ :=
  if hx : x = 0 then 0
  else l1Mass x.1 * f (normalize (toPosCone x hx))

@[simp] theorem perspective_zero {I : Type u} [Fintype I] [Nonempty I]
    (f : ProbVec I → ℝ) : perspective f (0 : ConeVec I) = 0 := by
  simp [perspective]

theorem perspective_of_ne {I : Type u} [Fintype I] [Nonempty I]
    (f : ProbVec I → ℝ) (x : ConeVec I) (hx : x ≠ 0) :
    perspective f x = l1Mass x.1 * f (normalize (toPosCone x hx)) := by
  simp [perspective, hx]

theorem perspective_posHomOne {I : Type u} [Fintype I] [Nonempty I]
    (f : ProbVec I → ℝ) : PosHomOne (perspective f) := by
  intro x c hc
  rcases hc.eq_or_lt with rfl | hcpos
  · have hzero : coneScale 0 (le_refl 0) x = 0 := by
      apply Subtype.ext
      funext i
      simp [coneScale]
    rw [hzero, perspective_zero]
    ring
  by_cases hx : x = 0
  · have hscaled : coneScale c hcpos.le x = 0 := by
      subst x
      apply Subtype.ext
      funext i
      simp [coneScale]
    rw [hscaled, perspective_zero, hx, perspective_zero]
    ring
  · have hscaled : coneScale c hcpos.le x ≠ 0 := by
      intro hzero
      have hval := congrArg (fun z : ConeVec I => z.1) hzero
      apply hx
      apply Subtype.ext
      funext i
      have hi : c * x.1 i = 0 := congrFun hval i
      exact (mul_eq_zero.mp hi).resolve_left hcpos.ne'
    rw [perspective_of_ne f _ hscaled, perspective_of_ne f x hx,
      l1Mass_coneScale]
    rw [toPosCone_coneScale c hcpos x hx, normalize_posScale]
    ring

@[simp] theorem l1Mass_coneMix {I : Type u} [Fintype I]
    (lambda : ℝ) (hlambda : lambda ∈ Icc (0 : ℝ) 1)
    (x z : ConeVec I) :
    l1Mass (coneMix lambda hlambda x z).1 =
      lambda * l1Mass x.1 + (1 - lambda) * l1Mass z.1 := by
  simp [l1Mass, coneMix, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Normalizing a cone mixture gives the mass-weighted simplex mixture of the
two normalized vectors. -/
theorem normalize_coneMix {I : Type u} [Fintype I] [Nonempty I]
    (x z : ConeVec I) (hx : x ≠ 0) (hz : z ≠ 0)
    (lambda : ℝ) (hlambda : lambda ∈ Icc (0 : ℝ) 1) :
    let mx := l1Mass x.1
    let mz := l1Mass z.1
    let s := lambda * mx + (1 - lambda) * mz
    let theta := lambda * mx / s
    ∃ hs : 0 < s, ∃ htheta : theta ∈ Icc (0 : ℝ) 1,
      normalize (toPosCone (coneMix lambda hlambda x z) (by
        apply (coneNonzeroMass (coneMix lambda hlambda x z)).mpr
        rw [l1Mass_coneMix]
        have hmx : 0 < l1Mass x.1 := (coneNonzeroMass x).mp hx
        have hmz : 0 < l1Mass z.1 := (coneNonzeroMass z).mp hz
        rcases hlambda.1.eq_or_lt with rfl | hlpos
        · simpa using hmz
        · exact add_pos_of_pos_of_nonneg (mul_pos hlpos hmx)
            (mul_nonneg (sub_nonneg.mpr hlambda.2) hmz.le))) =
        mixProbVec theta htheta
          (normalize (toPosCone x hx)) (normalize (toPosCone z hz)) := by
  dsimp only
  let mx := l1Mass x.1
  let mz := l1Mass z.1
  let s := lambda * mx + (1 - lambda) * mz
  let theta := lambda * mx / s
  have hmx : 0 < mx := (coneNonzeroMass x).mp hx
  have hmz : 0 < mz := (coneNonzeroMass z).mp hz
  have hs : 0 < s := by
    dsimp [s]
    rcases hlambda.1.eq_or_lt with rfl | hlpos
    · simpa using hmz
    · exact add_pos_of_pos_of_nonneg (mul_pos hlpos hmx)
        (mul_nonneg (sub_nonneg.mpr hlambda.2) hmz.le)
  have htheta0 : 0 ≤ theta := by
    exact div_nonneg (mul_nonneg hlambda.1 hmx.le) hs.le
  have hnumle : lambda * mx ≤ s := by
    exact le_add_of_nonneg_right
      (mul_nonneg (sub_nonneg.mpr hlambda.2) hmz.le)
  have htheta1 : theta ≤ 1 := (div_le_one hs).mpr hnumle
  let htheta : theta ∈ Icc (0 : ℝ) 1 := ⟨htheta0, htheta1⟩
  refine ⟨hs, htheta, ?_⟩
  have hmass : l1Mass (coneMix lambda hlambda x z).1 = s := by
    simp [s, mx, mz]
  apply Subtype.ext
  funext i
  change (lambda * x.1 i + (1 - lambda) * z.1 i) /
      l1Mass (coneMix lambda hlambda x z).1 =
    theta * (x.1 i / mx) + (1 - theta) * (z.1 i / mz)
  rw [hmass]
  dsimp [theta]
  field_simp [hmx.ne', hmz.ne', hs.ne']
  dsimp [s]
  ring

/-- The perspective of a concave simplex function is concave on the full
nonnegative cone. -/
theorem perspective_concaveCone {I : Type u} [Fintype I] [Nonempty I]
    (f : ProbVec I → ℝ) (hf : SimplexConcave f) :
    ConcaveCone (perspective f) := by
  apply (originExtension (perspective f) (perspective_zero f)
    (perspective_posHomOne f)).1
  intro x z hx hz lambda hlambda
  let mx := l1Mass x.1
  let mz := l1Mass z.1
  let s := lambda * mx + (1 - lambda) * mz
  let theta := lambda * mx / s
  obtain ⟨hs, htheta, hnormalize⟩ :=
    normalize_coneMix x z hx hz lambda hlambda
  have hmixne : coneMix lambda hlambda x z ≠ 0 := by
    apply (coneNonzeroMass (coneMix lambda hlambda x z)).mpr
    rw [l1Mass_coneMix]
    exact hs
  have hsimplex := hf (normalize (toPosCone x hx))
    (normalize (toPosCone z hz)) theta htheta
  have hscaled := mul_le_mul_of_nonneg_left hsimplex hs.le
  rw [perspective_of_ne f x hx, perspective_of_ne f z hz,
    perspective_of_ne f _ hmixne, l1Mass_coneMix, hnormalize]
  change lambda * (mx * f (normalize (toPosCone x hx))) +
      (1 - lambda) * (mz * f (normalize (toPosCone z hz))) ≤
    s * f (mixProbVec theta htheta
      (normalize (toPosCone x hx)) (normalize (toPosCone z hz)))
  have hstheta : s * theta = lambda * mx := by
    dsimp [theta]
    rw [mul_comm, div_mul_cancel₀ _ hs.ne']
  have hsone : s * (1 - theta) = (1 - lambda) * mz := by
    rw [mul_sub, mul_one, hstheta]
    dsimp [s]
    ring
  calc
    lambda * (mx * f (normalize (toPosCone x hx))) +
        (1 - lambda) * (mz * f (normalize (toPosCone z hz))) =
      (s * theta) * f (normalize (toPosCone x hx)) +
        (s * (1 - theta)) * f (normalize (toPosCone z hz)) := by
          rw [hstheta, hsone]
          ring
    _ = s * (theta * f (normalize (toPosCone x hx)) +
        (1 - theta) * f (normalize (toPosCone z hz))) := by ring
    _ ≤ s * f (mixProbVec theta htheta
        (normalize (toPosCone x hx)) (normalize (toPosCone z hz))) := hscaled

end ConditionalEntropy
