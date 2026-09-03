import BoundaryProofs.Curvature
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Exact finite-dimensional stationarity

This is the algebraic core of the exact stationarity correction packaged by
Lemma A.15 of the complete-proof document.  It turns a limiting stationary
direction into directions that are exactly stationary before the dimension
limit is taken.
-/

namespace ConditionalEntropy

theorem stationarityCorrection_dot
    {m : ℕ} (c z : Fin m → ℝ) (k : Fin m) (hk : c k ≠ 0) :
    let z' : Fin m → ℝ := fun j => if j = k then z j - (∑ i, c i * z i) / c k else z j
    ∑ i, c i * z' i = 0 := by
  dsimp
  classical
  let S : ℝ := ∑ i, c i * z i
  calc
    (∑ i, c i * if i = k then z i - S / c k else z i) =
        ∑ i, (c i * z i - if i = k then S else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = k
      · subst i
        simp only [if_pos]
        field_simp
      · simp [hi]
    _ = S - S := by
      rw [Finset.sum_sub_distrib]
      simp [S]
    _ = 0 := sub_self S

theorem stationarityCorrection_tendsto
    {m : ℕ} (c : ℕ → Fin m → ℝ) (cLimit z : Fin m → ℝ) (k : Fin m)
    (hc : ∀ i, Filter.Tendsto (fun d => c d i) Filter.atTop (nhds (cLimit i)))
    (hstationary : ∑ i, cLimit i * z i = 0) (hk : cLimit k ≠ 0) :
    Filter.Tendsto
      (fun d j => if j = k then z j - (∑ i, c d i * z i) / c d k else z j)
      Filter.atTop (nhds z) := by
  apply tendsto_pi_nhds.2
  intro j
  by_cases hj : j = k
  · subst j
    simp only [if_pos]
    have hsum : Filter.Tendsto (fun d => ∑ i, c d i * z i) Filter.atTop
        (nhds (∑ i, cLimit i * z i)) := by
      apply tendsto_finsetSum
      intro i _
      exact (hc i).mul_const (z i)
    rw [hstationary] at hsum
    simpa using tendsto_const_nhds.sub (hsum.div (hc k) hk)
  · simp only [if_neg hj]
    exact tendsto_const_nhds

end ConditionalEntropy
