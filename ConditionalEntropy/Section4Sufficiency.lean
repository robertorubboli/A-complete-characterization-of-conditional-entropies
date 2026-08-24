import ConditionalEntropy.GeneralSufficiency
import ConditionalEntropy.ShapeReduction
import ConditionalEntropy.TropicalShapeReduction
import ConditionalEntropy.LogSumExp
import ConditionalEntropy.CurvatureClosure
import ConditionalEntropy.RenyiSchur
import ConditionalEntropy.NullThresholds

/-!
# Section 4 sufficiency conclusions

This module closes the finite-temperature, tropical, and derivation
sufficiency arguments.  The tropical passages use the exact finite
log-sum-exp theorem on the (strictly positive) active column weights.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace ConditionalEntropy

universe u

/-- Literal finite-temperature sufficiency corollary. -/
theorem finiteTSufficiency
    (tau : ProbabilityMeasure Param) (t : ℝ) (h : DBulk t tau) :
    let hne := DBulk.ne h
    CMMonotone (HTemp t hne tau : PolyJointFunctional.{u}) := by
  dsimp only
  intro X Y Y' _ _ _ _ _ _ P Q hPQ
  rcases h with hpos | hneg | hexc
  · exact cmMonotoneAtRow_HTemp_of_concave X t hpos.1 tau
      ((generalSufficiency tau t (0 : Param)).1 hpos) P Q hPQ
  · exact cmMonotoneAtRow_HTemp_of_convex X t hneg.1 tau
      ((generalSufficiency tau t (0 : Param)).2.1 hneg) P Q hPQ
  · rcases hexc with ⟨astar, hexc⟩
    exact cmMonotoneAtRow_HTemp_of_convex X t hexc.1 tau
      ((generalSufficiency tau t astar).2.2 hexc) P Q hPQ

/-- Active column masses form a strictly positive finite probability family. -/
theorem activeColumnWeights
    {X Y : Type u} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (P : JointProb X Y) :
    (∀ y : Active P, 0 < colMass P y.1) ∧
      ∑ y : Active P, colMass P y.1 = 1 := by
  classical
  refine ⟨active_colMass_pos P, ?_⟩
  calc
    ∑ y : Active P, colMass P y.1 =
        ∑ y ∈ activeFinset P, colMass P y :=
      (Finset.sum_subtype (activeFinset P) (fun _ ↦ Iff.rfl)
        (fun y ↦ colMass P y)).symm
    _ = 1 := (positiveColumnsNonempty P).2

/-- The finite-temperature candidate is exactly log-sum-exp on active
conditioning columns. -/
theorem HTemp_eq_logSumExp
    {X Y : Type u} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y]
    (t : ℝ) (ht : t ≠ 0) (tau : ProbabilityMeasure Param)
    (P : JointProb X Y) :
    HTemp t ht tau P = logSumExp
      (fun y : Active P ↦ colMass P y.1)
      (fun y : Active P ↦
        integratedEntropyPos (probMeasure tau) (conditional P y)) t := by
  rfl

/-- Composition form of the negative log-sum-exp limit. -/
theorem tendsto_HTemp_comp_atBot
    {X Y : Type u} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y]
    (tau : ProbabilityMeasure Param) (P : JointProb X Y)
    (s : ℕ → ℝ) (hs : Tendsto s atTop atBot)
    (hne : ∀ n, s n ≠ 0) :
    Tendsto (fun n ↦ HTemp (s n) (hne n) tau P) atTop
      (𝓝 (HMinus tau P)) := by
  let p : Active P → ℝ := fun y ↦ colMass P y.1
  let a : Active P → ℝ := fun y ↦
    integratedEntropyPos (probMeasure tau) (conditional P y)
  have hlim := (tendsto_logSumExp_atBot p a
    (activeColumnWeights P).1 (activeColumnWeights P).2).comp hs
  simpa only [Function.comp_def, HTemp_eq_logSumExp, HMinus, p, a] using hlim

/-- Composition form of the positive log-sum-exp limit. -/
theorem tendsto_HTemp_comp_atTop
    {X Y : Type u} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y]
    (tau : ProbabilityMeasure Param) (P : JointProb X Y)
    (s : ℕ → ℝ) (hs : Tendsto s atTop atTop)
    (hne : ∀ n, s n ≠ 0) :
    Tendsto (fun n ↦ HTemp (s n) (hne n) tau P) atTop
      (𝓝 (HPlus tau P)) := by
  let p : Active P → ℝ := fun y ↦ colMass P y.1
  let a : Active P → ℝ := fun y ↦
    integratedEntropyPos (probMeasure tau) (conditional P y)
  have hlim := (tendsto_logSumExp_atTop p a
    (activeColumnWeights P).1 (activeColumnWeights P).2).comp hs
  simpa only [Function.comp_def, HTemp_eq_logSumExp, HPlus, p, a] using hlim

/-- Pointwise convergence commutes with a finite nonempty minimum. -/
theorem tendsto_finMin_of_pointwise
    {J : Type u} [Fintype J] [Nonempty J]
    (aN : ℕ → J → ℝ) (a : J → ℝ)
    (h : ∀ j, Tendsto (fun n ↦ aN n j) atTop (𝓝 (a j))) :
    Tendsto (fun n ↦ finMin (aN n)) atTop (𝓝 (finMin a)) := by
  classical
  unfold finMin
  exact Tendsto.finset_inf'_nhds_apply Finset.univ_nonempty
    (fun j _ ↦ h j)

/-- Pointwise convergence commutes with a finite nonempty maximum. -/
theorem tendsto_finMax_of_pointwise
    {J : Type u} [Fintype J] [Nonempty J]
    (aN : ℕ → J → ℝ) (a : J → ℝ)
    (h : ∀ j, Tendsto (fun n ↦ aN n j) atTop (𝓝 (a j))) :
    Tendsto (fun n ↦ finMax (aN n)) atTop (𝓝 (finMax a)) := by
  classical
  unfold finMax
  exact Tendsto.finset_sup'_nhds_apply Finset.univ_nonempty
    (fun j _ ↦ h j)

/-- The standard total negative-temperature sequence tends to minus infinity. -/
theorem tendsto_tNeg :
    Tendsto (fun n : ℕ ↦ -((n : ℝ) + 1)) atTop atBot := by
  exact tendsto_neg_atTop_atBot.comp
    (tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop (R := ℝ)))

/-- The standard total positive-temperature sequence tends to plus infinity. -/
theorem tendsto_tPos :
    Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
  tendsto_atTop_add_const_right atTop 1
    (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Negative tropical sufficiency in the all-lower-support branch. -/
theorem negativeTropicalSufficiency_lower
    (tau : ProbabilityMeasure Param)
    (hsupp : suppMeasure (probMeasure tau) ⊆ Icc (0 : Param) 1) :
    CMMonotone (HMinus tau : PolyJointFunctional.{u}) := by
  intro X Y Y' _ _ _ _ _ _ P Q hPQ
  let s : ℕ → ℝ := fun n ↦ -((n : ℝ) + 1)
  have hs : Tendsto s atTop atBot := tendsto_tNeg
  have hne : ∀ n, s n ≠ 0 := by
    intro n
    dsimp only [s]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  apply le_of_tendsto_of_tendsto'
    (tendsto_HTemp_comp_atBot tau P s hs hne)
    (tendsto_HTemp_comp_atBot tau Q s hs hne)
  intro n
  have hsn : s n < 0 := by
    dsimp only [s]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  exact finiteTSufficiency tau (s n)
    (Or.inr (Or.inl ⟨hsn, hsupp⟩)) P Q hPQ

/-- Exceptional negative-tropical sufficiency when the guarded real moment is
strictly negative.  Scaling the temperature sequence by that moment makes
every term admissible, so no eventual-tail reindexing is needed. -/
theorem negativeTropicalSufficiency_exceptional_neg
    (tau : ProbabilityMeasure Param) (astar : Param)
    (hexc : NegTropExcAdm tau astar)
    (hmneg : MReal (probMeasure tau) < 0) :
    CMMonotone (HMinus tau : PolyJointFunctional.{u}) := by
  rcases hexc with ⟨hastar, hsupp, hone, hLower, hMom, _hmoment⟩
  let m : ℝ := MReal (probMeasure tau)
  let s : ℕ → ℝ := fun n ↦ (1 / m) * ((n : ℝ) + 1)
  have hm : m < 0 := hmneg
  have hc : 1 / m < 0 := one_div_neg.mpr hm
  have hs : Tendsto s atTop atBot := by
    have hbase : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_tPos
    simpa only [s] using hbase.const_mul_atTop_of_neg hc
  have hne : ∀ n, s n ≠ 0 := by
    intro n
    dsimp only [s]
    exact mul_ne_zero (one_div_ne_zero hm.ne)
      (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
  intro X Y Y' _ _ _ _ _ _ P Q hPQ
  apply le_of_tendsto_of_tendsto'
    (tendsto_HTemp_comp_atBot tau P s hs hne)
    (tendsto_HTemp_comp_atBot tau Q s hs hne)
  intro n
  have hn : 0 < (n : ℝ) + 1 := by
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hsn : s n < 0 := by
    exact mul_neg_of_neg_of_pos hc hn
  have hinv : 1 / s n = m / ((n : ℝ) + 1) := by
    dsimp only [s]
    field_simp [hm.ne, hn.ne']
  have hmmul : m * (n : ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hm.le (Nat.cast_nonneg n)
  have hmoment : MReal (probMeasure tau) ≤ 1 / s n := by
    change m ≤ 1 / s n
    rw [hinv, le_div_iff₀ hn]
    nlinarith
  exact finiteTSufficiency tau (s n)
    (Or.inr (Or.inr ⟨astar,
      ⟨hsn, hastar, hsupp, hone, hLower, hMom, hmoment⟩⟩)) P Q hPQ

@[simp] theorem probMeasure_probMix
    (tau rho : ProbabilityMeasure Param) (eps : ℝ)
    (heps : 0 ≤ eps ∧ eps ≤ 1) :
    probMeasure (probMix tau rho eps heps) =
      ENNReal.ofReal (1 - eps) • probMeasure tau +
        ENNReal.ofReal eps • probMeasure rho := rfl

/-- Additivity of the guarded real moment when both one-sided moment pairs
are finite. -/
theorem MReal_add_of_MomFin (nu rho : Measure Param)
    (hnu : MomFin nu) (hrho : MomFin rho) :
    MReal (nu + rho) = MReal nu + MReal rho := by
  unfold MReal
  rw [MLower_add, MUpper_add,
    ENNReal.toReal_add hnu.1.ne hrho.1.ne,
    ENNReal.toReal_add hnu.2.ne hrho.2.ne]
  ring

/-- The real guarded moment of an upper Dirac mass is its (negative)
singular weight. -/
theorem MReal_dirac_of_one_lt (astar : Param) (hastar : 1 < astar) :
    MReal (diracRaw astar) = singularWeight astar := by
  unfold MReal
  rw [MLower_dirac, MUpper_dirac, omegaLower_of_one_lt hastar,
    toReal_omegaUpper_of_one_lt hastar]
  simp

/-- Exact affine integration identity for a probability mixture. -/
theorem integratedEntropyPos_probMix
    {I : Type u} [Fintype I] [Nonempty I]
    (tau rho : ProbabilityMeasure Param) (eps : ℝ)
    (heps : 0 ≤ eps ∧ eps ≤ 1) (p : ProbVec I) :
    integratedEntropyPos (probMeasure (probMix tau rho eps heps)) p =
      (1 - eps) * integratedEntropyPos (probMeasure tau) p +
        eps * integratedEntropyPos (probMeasure rho) p := by
  letI : IsFiniteMeasure (probMeasure tau) := by
    unfold probMeasure
    infer_instance
  letI : IsFiniteMeasure (probMeasure rho) := by
    unfold probMeasure
    infer_instance
  letI : IsFiniteMeasure
      (ENNReal.ofReal (1 - eps) • probMeasure tau) :=
    (probMeasure tau).smul_finite ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure
      (ENNReal.ofReal eps • probMeasure rho) :=
    (probMeasure rho).smul_finite ENNReal.ofReal_ne_top
  unfold integratedEntropyPos
  rw [probMeasure_probMix,
    integral_add_measure (integrable_renyi _ p) (integrable_renyi _ p),
    integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (sub_nonneg.mpr heps.2),
    ENNReal.toReal_ofReal heps.1]
  rfl

/-- A positive mixture with the exceptional upper atom preserves all
negative-tropical exceptional clauses and makes the guarded moment strictly
negative. -/
theorem probMix_exceptional_preserves
    (tau : ProbabilityMeasure Param) (astar : Param)
    (hexc : NegTropExcAdm tau astar)
    (eps : ℝ) (heps : 0 ≤ eps ∧ eps ≤ 1)
    (hepsPos : 0 < eps) (hepsLt : eps < 1) :
    let tauMix := probMix tau (diracProb astar) eps heps
    NegTropExcAdm tauMix astar ∧
      MReal (probMeasure tauMix) < 0 := by
  dsimp only
  rcases hexc with ⟨hastar, hsupp, hone, _hLower, hMom, hmoment⟩
  have hleftPos : 0 < ENNReal.ofReal (1 - eps) :=
    ENNReal.ofReal_pos.mpr (sub_pos.mpr hepsLt)
  have hrightPos : 0 < ENNReal.ofReal eps :=
    ENNReal.ofReal_pos.mpr hepsPos
  have hdirMom : MomFin (probMeasure (diracProb astar)) := by
    change MomFin (diracRaw astar)
    exact MomFin_dirac astar
  have hleftMom : MomFin
      (ENNReal.ofReal (1 - eps) • probMeasure tau) := by
    exact (MomFin_smul_iff (sub_pos.mpr hepsLt) (probMeasure tau)).2 hMom
  have hrightMom : MomFin
      (ENNReal.ofReal eps • probMeasure (diracProb astar)) := by
    exact (MomFin_smul_iff hepsPos (probMeasure (diracProb astar))).2 hdirMom
  have hmixMom : MomFin
      (probMeasure (probMix tau (diracProb astar) eps heps)) := by
    rw [probMeasure_probMix]
    constructor
    · rw [MLower_add]
      exact ENNReal.add_lt_top.mpr ⟨hleftMom.1, hrightMom.1⟩
    · rw [MUpper_add]
      exact ENNReal.add_lt_top.mpr ⟨hleftMom.2, hrightMom.2⟩
  have hsupport :
      suppMeasure (probMeasure (probMix tau (diracProb astar) eps heps)) ⊆
        Icc (0 : Param) 1 ∪ {astar} := by
    rw [probMeasure_probMix, suppMeasure, Measure.support_add,
      support_smul_of_pos _ hleftPos,
      support_smul_of_pos _ hrightPos,
      show probMeasure (diracProb astar) = diracRaw astar from rfl,
      support_diracRaw]
    intro a ha
    rcases ha with ha | ha
    · exact hsupp ha
    · exact Or.inr ha
  have honeDirac : probMeasure (diracProb astar) ({1} : Set Param) = 0 := by
    change diracRaw astar ({1} : Set Param) = 0
    rw [diracRaw_apply astar (measurableSet_singleton (1 : Param))]
    simp [ne_of_gt hastar]
  have honeMix :
      probMeasure (probMix tau (diracProb astar) eps heps)
        ({1} : Set Param) = 0 := by
    rw [probMeasure_probMix, Measure.add_apply,
      Measure.smul_apply, Measure.smul_apply]
    simp [hone, honeDirac]
  have hformula :
      MReal (probMeasure (probMix tau (diracProb astar) eps heps)) =
        (1 - eps) * MReal (probMeasure tau) +
          eps * singularWeight astar := by
    rw [probMeasure_probMix,
      MReal_add_of_MomFin _ _ hleftMom hrightMom,
      MReal_smul (sub_nonneg.mpr heps.2),
      MReal_smul heps.1,
      show probMeasure (diracProb astar) = diracRaw astar from rfl,
      MReal_dirac_of_one_lt astar hastar]
  have hfirst : (1 - eps) * MReal (probMeasure tau) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr heps.2) hmoment
  have hsecond : eps * singularWeight astar < 0 :=
    mul_neg_of_pos_of_neg hepsPos (singularWeight_neg_of_one_lt hastar)
  have hstrict :
      MReal (probMeasure (probMix tau (diracProb astar) eps heps)) < 0 := by
    rw [hformula]
    linarith
  exact ⟨⟨hastar, hsupport, honeMix, hmixMom.1, hmixMom,
    hstrict.le⟩, hstrict⟩

/-- The manuscript's complete negative tropical sufficiency proposition. -/
theorem negativeTropicalSufficiency
    (tau : ProbabilityMeasure Param) :
    DMinus tau → CMMonotone (HMinus tau : PolyJointFunctional.{u}) := by
  rintro (hlower | ⟨astar, hexc⟩)
  · exact negativeTropicalSufficiency_lower tau hlower
  · rcases lt_or_eq_of_le hexc.2.2.2.2.2 with hmneg | hmzero
    · exact negativeTropicalSufficiency_exceptional_neg tau astar hexc hmneg
    · let eps : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 2)
      have hepsPos : ∀ n, 0 < eps n := by
        intro n
        dsimp only [eps]
        positivity
      have hepsLt : ∀ n, eps n < 1 := by
        intro n
        dsimp only [eps]
        rw [div_lt_one]
        · have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        · positivity
      have heps : ∀ n, 0 ≤ eps n ∧ eps n ≤ 1 :=
        fun n ↦ ⟨(hepsPos n).le, (hepsLt n).le⟩
      let tauN : ℕ → ProbabilityMeasure Param := fun n ↦
        probMix tau (diracProb astar) (eps n) (heps n)
      have hepsLim : Tendsto eps atTop (𝓝 0) := by
        have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
          tendsto_atTop_add_const_right atTop 2
            (tendsto_natCast_atTop_atTop (R := ℝ))
        exact tendsto_const_nhds.div_atTop hden
      have hent {I : Type u} [Fintype I] [Nonempty I] (p : ProbVec I) :
          Tendsto
            (fun n ↦ integratedEntropyPos (probMeasure (tauN n)) p)
            atTop (𝓝 (integratedEntropyPos (probMeasure tau) p)) := by
        have honeLim : Tendsto (fun n : ℕ ↦ (1 : ℝ) - eps n) atTop
            (𝓝 (1 - 0)) :=
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ))
            atTop (𝓝 1)).sub hepsLim
        have hcalc :=
          honeLim.mul_const
              (integratedEntropyPos (probMeasure tau) p) |>.add
            (hepsLim.mul_const
              (integratedEntropyPos (probMeasure (diracProb astar)) p))
        simpa only [tauN, integratedEntropyPos_probMix, sub_zero, one_mul,
          zero_mul, add_zero] using hcalc
      intro X Y Y' _ _ _ _ _ _ P Q hPQ
      have hlimP : Tendsto (fun n ↦ HMinus (tauN n) P) atTop
          (𝓝 (HMinus tau P)) := by
        change Tendsto
          (fun n ↦ finMin (fun y : Active P ↦
            integratedEntropyPos (probMeasure (tauN n)) (conditional P y)))
          atTop (𝓝 (finMin (fun y : Active P ↦
            integratedEntropyPos (probMeasure tau) (conditional P y))))
        exact tendsto_finMin_of_pointwise _ _ (fun y ↦ hent (conditional P y))
      have hlimQ : Tendsto (fun n ↦ HMinus (tauN n) Q) atTop
          (𝓝 (HMinus tau Q)) := by
        change Tendsto
          (fun n ↦ finMin (fun y : Active Q ↦
            integratedEntropyPos (probMeasure (tauN n)) (conditional Q y)))
          atTop (𝓝 (finMin (fun y : Active Q ↦
            integratedEntropyPos (probMeasure tau) (conditional Q y))))
        exact tendsto_finMin_of_pointwise _ _ (fun y ↦ hent (conditional Q y))
      apply le_of_tendsto_of_tendsto' hlimP hlimQ
      intro n
      have hdata := probMix_exceptional_preserves tau astar hexc
        (eps n) (heps n) (hepsPos n) (hepsLt n)
      exact negativeTropicalSufficiency_exceptional_neg
        (tauN n) astar hdata.1 hdata.2 P Q hPQ

/-- Positive tropical component formula. -/
theorem positiveTropicalComponent
    {X Y : Type u} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] (P : JointProb X Y) :
    HPlus (diracProb 0) P =
      (letI := activeNonempty P
       finMax (fun y : Active P ↦ renyi 0 (conditional P y))) := by
  change finMax (fun y : Active P ↦
      integratedEntropyPos (diracRaw 0) (conditional P y)) = _
  simp only [integratedEntropyPos_dirac]

/-- Positive tropical sufficiency. -/
theorem positiveTropicalSufficiency :
    CMMonotone
      (HPlus (diracProb 0) : PolyJointFunctional.{u}) := by
  intro X Y Y' _ _ _ _ _ _ P Q hPQ
  let s : ℕ → ℝ := fun n ↦ (n : ℝ) + 1
  have hs : Tendsto s atTop atTop := tendsto_tPos
  have hne : ∀ n, s n ≠ 0 := by
    intro n
    dsimp only [s]
    positivity
  apply le_of_tendsto_of_tendsto'
    (tendsto_HTemp_comp_atTop (diracProb 0) P s hs hne)
    (tendsto_HTemp_comp_atTop (diracProb 0) Q s hs hne)
  intro n
  have hsupp : suppMeasure (probMeasure (diracProb 0)) ⊆
      Icc (0 : Param) 1 := by
    rw [show probMeasure (diracProb 0) = diracRaw 0 from rfl,
      suppMeasure, support_diracRaw]
    simp
  have hone : probMeasure (diracProb 0) ({1} : Set Param) = 0 := by
    rw [show probMeasure (diracProb 0) = diracRaw 0 from rfl,
      diracRaw_apply 0 (measurableSet_singleton (1 : Param))]
    simp
  have hmoment : MLower (probMeasure (diracProb 0)) ≤
      ENNReal.ofReal (1 / s n) := by
    rw [show probMeasure (diracProb 0) = diracRaw 0 from rfl,
      MLower_dirac, omegaLower_zero]
    exact bot_le
  exact finiteTSufficiency (diracProb 0) (s n)
    (Or.inl ⟨by dsimp [s]; positivity, hsupp, hone, hmoment⟩) P Q hPQ

/-- Derivation polymorphic family from the manuscript. -/
def derivationFamily (sigma : FiniteMeasure Param) :
    PolyJointFunctional.{u} :=
  fun P ↦ by
    classical
    exact ∑ y : Active P, colMass P y.1 *
      integratedEntropyPos (finiteMeasure sigma) (conditional P y)

/-- The derivation column is the positive integral of the individual Renyi
perspectives. -/
theorem columnDeriv_eq_integratePerspective
    (sigma : FiniteMeasure Param)
    {I : Type u} [Fintype I] [Nonempty I] (x : ConeVec I) :
    columnDeriv sigma x = integrateConeFamily (finiteMeasure sigma)
      (fun a ↦ perspective (renyi a : ProbVec I → ℝ)) x := by
  by_cases hx : x = 0
  · subst x
    simp [integrateConeFamily]
  · rw [columnDeriv_of_ne sigma x hx]
    unfold integrateConeFamily
    simp_rw [perspective_of_ne (renyi _ : ProbVec I → ℝ) x hx]
    rw [integral_const_mul]
    rfl

/-- Derivation sufficiency and the exact polymorphic identification. -/
theorem derivationSufficiency
    (sigma : FiniteMeasure Param)
    (hsupp : suppMeasure (finiteMeasure sigma) ⊆ Icc (0 : Param) 1) :
    CMMonotone (derivationFamily sigma : PolyJointFunctional.{u}) ∧
      (derivationFamily sigma : PolyJointFunctional.{u}) =
        (HZero sigma : PolyJointFunctional.{u}) := by
  letI : IsFiniteMeasure (finiteMeasure sigma) := by
    unfold finiteMeasure
    infer_instance
  have hcurv : ∀ {I : Type u} [Fintype I] [Nonempty I],
      ConcaveCone (columnDeriv sigma : ConeVec I → ℝ) := by
    intro I _ _
    let F : Param → ConeVec I → ℝ :=
      fun a ↦ perspective (renyi a : ProbVec I → ℝ)
    have hmeas : ∀ x : ConeVec I,
        Measurable (fun a ↦ F a x) ∧
          Integrable (fun a ↦ F a x) (finiteMeasure sigma) := by
      intro x
      by_cases hx : x = 0
      · subst x
        simp [F]
      · have heq : (fun a ↦ F a x) = fun a ↦
            l1Mass x.1 * renyi a (normalize (toPosCone x hx)) := by
          funext a
          exact perspective_of_ne (renyi a : ProbVec I → ℝ) x hx
        rw [heq]
        exact ⟨measurable_const.mul
            (measurable_renyi (normalize (toPosCone x hx))),
          (integrable_renyi (finiteMeasure sigma)
            (normalize (toPosCone x hx))).const_mul _⟩
    have hae : ∀ᵐ a ∂finiteMeasure sigma, ConcaveCone (F a) := by
      filter_upwards [Measure.support_mem_ae
        (μ := finiteMeasure sigma)] with a ha
      exact perspective_concaveCone (renyi a : ProbVec I → ℝ)
        (renyiSimplexConcave a (hsupp ha).2)
    change ConcaveCone (fun x : ConeVec I ↦ columnDeriv sigma x)
    rw [funext fun x ↦ columnDeriv_eq_integratePerspective sigma x]
    exact (integrationCurvature (finiteMeasure sigma) F hmeas).1 hae
  constructor
  · intro X Y Y' _ _ _ _ _ _ P Q hPQ
    change HZero sigma P ≤ HZero sigma Q
    exact cmMonotoneAtRow_HZero_of_concave X sigma hcurv P Q hPQ
  · rfl

end ConditionalEntropy
