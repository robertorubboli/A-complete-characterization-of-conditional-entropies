import ConditionalEntropy.ShannonDedicatedEscort
import ConditionalEntropy.CompactUniform
import ConditionalEntropy.ShannonLogMass
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform expansion at the Shannon order

The rounded three-block family has two large blocks whose normalized masses
converge to `theta.q` and `theta.p`, and one vanishing block.  We keep the
rounding errors as coordinates of a finite-dimensional smooth model.  This
is useful because the factors of `log (shannonScale n)` that occur in the
entropy are then represented by two coordinates which themselves converge
to zero.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace ConditionalEntropy

/-! ## A common positive line interval -/

/-- Compactness gives one positive interval for every Shannon line in the
family, uniformly in the scale. -/
private theorem exists_uniform_shannonLinePositive (theta : ShannonData)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) :
    ∃ lambda0 : ℝ, 0 < lambda0 ∧
      ∀ (n : ℕ) (z : ℝ × ℝ), z ∈ K →
        letI := shannonIndexNonempty theta n
        ∀ lambda ∈ Icc (-lambda0) lambda0,
          LinePositive (shannonLineData theta n z) lambda := by
  obtain ⟨U, hU, hvel⟩ := exists_uniform_shannonVelocity_bound theta K hK
  let lambda0 : ℝ := 1 / (2 * (U + 1))
  have hden : 0 < 2 * (U + 1) := by positivity
  have hlambda0 : 0 < lambda0 := one_div_pos.mpr hden
  refine ⟨lambda0, hlambda0, ?_⟩
  intro n z hz
  letI := shannonIndexNonempty theta n
  intro lambda hlambda i
  have hlambdaAbs : |lambda| ≤ lambda0 := by
    rw [abs_le]
    exact hlambda
  have hvelocity : |shannonVelocity theta n z i| ≤ U := by
    simpa only [shannonVelocity_eq_blockRepresentative] using
      hvel n z hz i.1
  have hUhalf : U * lambda0 < 1 := by
    dsimp only [lambda0]
    have hlt : U < 2 * (U + 1) := by linarith
    simpa only [div_eq_mul_inv, one_mul] using (div_lt_one hden).2 hlt
  have hproduct :
      |shannonVelocity theta n z i * lambda| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul hvelocity hlambdaAbs (abs_nonneg _)
      hU).trans_lt hUhalf
  have hfactor : 0 < 1 + shannonVelocity theta n z i * lambda := by
    have hlower := (neg_lt_of_abs_lt hproduct)
    linarith [hlower]
  exact mul_pos (shannonBase_pos theta n z i) hfactor

/-! ## The normalized six-coordinate expansion model -/

/-- The coordinates are the three normalized block masses, the two
logarithm-weighted rounding errors, and the reciprocal logarithmic scale. -/
abbrev ShannonExpansionCoeffs := Fin 6 → ℝ

def shannonExpansionA (theta : ShannonData) (xi : ShannonExpansionCoeffs)
    (z : ℝ × ℝ) (lambda : ℝ) : ℝ :=
  theta.q + z.1 * lambda * xi 5

def shannonExpansionB (theta : ShannonData) (xi : ShannonExpansionCoeffs)
    (z : ℝ × ℝ) (lambda : ℝ) : ℝ :=
  theta.p - z.1 * lambda * xi 5

def shannonExpansionC (_xi : ShannonExpansionCoeffs)
    (z : ℝ × ℝ) (lambda : ℝ) : ℝ :=
  1 + z.2 * lambda

def shannonExpansionTotal (theta : ShannonData)
    (xi : ShannonExpansionCoeffs) (z : ℝ × ℝ) (lambda : ℝ) : ℝ :=
  xi 0 * shannonExpansionA theta xi z lambda +
    xi 1 * shannonExpansionB theta xi z lambda +
    xi 2 * shannonExpansionC xi z lambda

/-- Exact normalized entropy error as a smooth function of the rounding
coordinates. -/
def shannonExpansionModel (theta : ShannonData)
    (x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ)) : ℝ :=
  let xi := x.1
  let z := x.2.1
  let lambda := x.2.2
  let a := shannonExpansionA theta xi z lambda
  let b := shannonExpansionB theta xi z lambda
  let c := shannonExpansionC xi z lambda
  let T := shannonExpansionTotal theta xi z lambda
  Real.log T + (a * b * xi 3 + c * (b - 2) * xi 4) / T -
      (xi 0 * a * Real.log a + xi 1 * b * Real.log b +
        xi 2 * c * Real.log c) / T +
    a * Real.log a + b * Real.log b

/-- Open positivity domain of the normalized entropy model. -/
def shannonExpansionDomain (theta : ShannonData) :
    Set (ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ)) :=
  {x | 0 < shannonExpansionA theta x.1 x.2.1 x.2.2 ∧
    0 < shannonExpansionB theta x.1 x.2.1 x.2.2 ∧
    0 < shannonExpansionC x.1 x.2.1 x.2.2 ∧
    0 < shannonExpansionTotal theta x.1 x.2.1 x.2.2}

private theorem isOpen_shannonExpansionDomain (theta : ShannonData) :
    IsOpen (shannonExpansionDomain theta) := by
  unfold shannonExpansionDomain
  change IsOpen
    ({x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) |
        (0 : ℝ) < shannonExpansionA theta x.1 x.2.1 x.2.2} ∩
      ({x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) |
          (0 : ℝ) < shannonExpansionB theta x.1 x.2.1 x.2.2} ∩
        ({x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) |
            (0 : ℝ) < shannonExpansionC x.1 x.2.1 x.2.2} ∩
          {x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) | (0 : ℝ) <
            shannonExpansionTotal theta x.1 x.2.1 x.2.2})))
  exact (isOpen_lt continuous_const (by
      unfold shannonExpansionA
      fun_prop)).inter
    ((isOpen_lt continuous_const (by
      unfold shannonExpansionB
      fun_prop)).inter
      ((isOpen_lt continuous_const (by
        unfold shannonExpansionC
        fun_prop)).inter
        (isOpen_lt continuous_const (by
          unfold shannonExpansionTotal shannonExpansionA
            shannonExpansionB shannonExpansionC
          fun_prop))))

private theorem contDiffOn_shannonExpansionModel (theta : ShannonData) :
    ContDiffOn ℝ ⊤ (shannonExpansionModel theta)
      (shannonExpansionDomain theta) := by
  have ha : ContDiffOn ℝ ⊤
      (fun x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) ↦
        shannonExpansionA theta x.1 x.2.1 x.2.2)
      (shannonExpansionDomain theta) := by
    unfold shannonExpansionA
    fun_prop
  have hb : ContDiffOn ℝ ⊤
      (fun x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) ↦
        shannonExpansionB theta x.1 x.2.1 x.2.2)
      (shannonExpansionDomain theta) := by
    unfold shannonExpansionB
    fun_prop
  have hc : ContDiffOn ℝ ⊤
      (fun x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) ↦
        shannonExpansionC x.1 x.2.1 x.2.2)
      (shannonExpansionDomain theta) := by
    unfold shannonExpansionC
    fun_prop
  have hT : ContDiffOn ℝ ⊤
      (fun x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) ↦
        shannonExpansionTotal theta x.1 x.2.1 x.2.2)
      (shannonExpansionDomain theta) := by
    unfold shannonExpansionTotal shannonExpansionA shannonExpansionB
      shannonExpansionC
    fun_prop
  have ha0 : ∀ x ∈ shannonExpansionDomain theta,
      (fun y : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) ↦
        shannonExpansionA theta y.1 y.2.1 y.2.2) x ≠ 0 :=
    fun x hx ↦ hx.1.ne'
  have hb0 : ∀ x ∈ shannonExpansionDomain theta,
      (fun y : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) ↦
        shannonExpansionB theta y.1 y.2.1 y.2.2) x ≠ 0 :=
    fun x hx ↦ hx.2.1.ne'
  have hc0 : ∀ x ∈ shannonExpansionDomain theta,
      (fun y : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) ↦
        shannonExpansionC y.1 y.2.1 y.2.2) x ≠ 0 :=
    fun x hx ↦ hx.2.2.1.ne'
  have hT0 : ∀ x ∈ shannonExpansionDomain theta,
      (fun y : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) ↦
        shannonExpansionTotal theta y.1 y.2.1 y.2.2) x ≠ 0 :=
    fun x hx ↦ hx.2.2.2.ne'
  have hxi0 : ContDiffOn ℝ ⊤
      (fun x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) ↦ x.1 0)
      (shannonExpansionDomain theta) := by fun_prop
  have hxi1 : ContDiffOn ℝ ⊤
      (fun x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) ↦ x.1 1)
      (shannonExpansionDomain theta) := by fun_prop
  have hxi2 : ContDiffOn ℝ ⊤
      (fun x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) ↦ x.1 2)
      (shannonExpansionDomain theta) := by fun_prop
  have hxi3 : ContDiffOn ℝ ⊤
      (fun x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) ↦ x.1 3)
      (shannonExpansionDomain theta) := by fun_prop
  have hxi4 : ContDiffOn ℝ ⊤
      (fun x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) ↦ x.1 4)
      (shannonExpansionDomain theta) := by fun_prop
  have htwo : ContDiffOn ℝ ⊤
      (fun _x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) ↦ (2 : ℝ))
      (shannonExpansionDomain theta) := by fun_prop
  have hweighted : ContDiffOn ℝ ⊤
      (fun x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) ↦
        shannonExpansionA theta x.1 x.2.1 x.2.2 *
            shannonExpansionB theta x.1 x.2.1 x.2.2 * x.1 3 +
          shannonExpansionC x.1 x.2.1 x.2.2 *
            (shannonExpansionB theta x.1 x.2.1 x.2.2 - 2) * x.1 4)
      (shannonExpansionDomain theta) :=
    ((ha.mul hb).mul hxi3).add ((hc.mul (hb.sub htwo)).mul hxi4)
  have hlogs : ContDiffOn ℝ ⊤
      (fun x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) ↦
        x.1 0 * shannonExpansionA theta x.1 x.2.1 x.2.2 *
            Real.log (shannonExpansionA theta x.1 x.2.1 x.2.2) +
          x.1 1 * shannonExpansionB theta x.1 x.2.1 x.2.2 *
            Real.log (shannonExpansionB theta x.1 x.2.1 x.2.2) +
          x.1 2 * shannonExpansionC x.1 x.2.1 x.2.2 *
            Real.log (shannonExpansionC x.1 x.2.1 x.2.2))
      (shannonExpansionDomain theta) :=
    (((hxi0.mul ha).mul (ha.log ha0)).add
      ((hxi1.mul hb).mul (hb.log hb0))).add
        ((hxi2.mul hc).mul (hc.log hc0))
  have hbaseLogs : ContDiffOn ℝ ⊤
      (fun x : ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ) ↦
        shannonExpansionA theta x.1 x.2.1 x.2.2 *
            Real.log (shannonExpansionA theta x.1 x.2.1 x.2.2) +
          shannonExpansionB theta x.1 x.2.1 x.2.2 *
            Real.log (shannonExpansionB theta x.1 x.2.1 x.2.2))
      (shannonExpansionDomain theta) :=
    (ha.mul (ha.log ha0)).add (hb.mul (hb.log hb0))
  unfold shannonExpansionModel
  dsimp only
  have hcombined := (((hT.log hT0).add (hweighted.div hT hT0)).sub
    (hlogs.div hT hT0)).add hbaseLogs
  apply hcombined.congr
  intro x _hx
  simp only [Pi.div_apply]
  ring

/-- Actual rounding coordinates of scale `n`. -/
def shannonRoundRatio (s : ℝ) (n : ℕ) : ℝ :=
  (Nat.ceil (Real.rpow (shannonScale n) s) : ℝ) /
    Real.rpow (shannonScale n) s

def shannonExpansionActual (theta : ShannonData) (n : ℕ) :
    ShannonExpansionCoeffs :=
  let d := shannonScale n
  let r0 := shannonRoundRatio theta.R n
  let r1 := shannonRoundRatio (theta.R - 1) n
  let r2 := shannonRoundRatio (theta.R - 1 - theta.c) n *
    Real.rpow d (1 - theta.c)
  ![r0, r1, r2, shannonLogScale n * (r0 - r1),
    shannonLogScale n * r2, (shannonLogScale n)⁻¹]

/-- Ideal coordinates at the same reciprocal logarithmic scale. -/
def shannonExpansionIdeal (n : ℕ) : ShannonExpansionCoeffs :=
  ![1, 1, 0, 0, 0, (shannonLogScale n)⁻¹]

/-- Common limit of the actual and ideal coordinate sequences. -/
def shannonExpansionLimit : ShannonExpansionCoeffs :=
  ![1, 1, 0, 0, 0, 0]

private theorem tendsto_shannonRoundRatio (s : ℝ) (hs : 0 < s) :
    Tendsto (shannonRoundRatio s) atTop (𝓝 1) := by
  have hpow : Tendsto
      (fun n : ℕ ↦ Real.rpow (shannonScale n) (-s)) atTop (𝓝 0) := by
    have hbase : Tendsto
        (fun n : ℕ ↦ Real.rpow (blockScale n) (-s)) atTop (𝓝 0) := by
      exact (tendsto_rpow_neg_atTop hs).comp tendsto_blockScale_atTop
    simpa only [shannonScale] using hbase
  have hupper : Tendsto
      (fun n : ℕ ↦ 1 + Real.rpow (shannonScale n) (-s))
      atTop (𝓝 1) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add hpow : Tendsto
        (fun n : ℕ ↦ 1 + Real.rpow (shannonScale n) (-s))
        atTop (𝓝 (1 + 0)))
  refine .squeeze tendsto_const_nhds
    hupper ?_ ?_
  · intro n
    have h := ceil_rpow_ratio_bounds s (n + 2) hs (by omega)
    simpa only [shannonRoundRatio, shannonScale, blockScale,
      Nat.cast_add, Nat.cast_ofNat] using h.1
  · intro n
    have h := ceil_rpow_ratio_bounds s (n + 2) hs (by omega)
    simpa only [shannonRoundRatio, shannonScale, blockScale,
      Nat.cast_add, Nat.cast_ofNat] using h.2

private theorem tendsto_shannonLogScale_mul_rpow_neg (s : ℝ)
    (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ shannonLogScale n *
      Real.rpow (shannonScale n) (-s)) atTop (𝓝 0) := by
  have hwhole := tendsto_one_add_log_mul_rpow_blockScale s hs
  have hpow : Tendsto
      (fun n : ℕ ↦ Real.rpow (shannonScale n) (-s)) atTop (𝓝 0) := by
    have hbase : Tendsto
        (fun n : ℕ ↦ Real.rpow (blockScale n) (-s)) atTop (𝓝 0) := by
      exact (tendsto_rpow_neg_atTop hs).comp tendsto_blockScale_atTop
    simpa only [shannonScale] using hbase
  have hsub := hwhole.sub hpow
  have heq :
      (fun n : ℕ ↦ shannonLogScale n *
          Real.rpow (shannonScale n) (-s)) =
        (fun n : ℕ ↦
          (1 + Real.log (blockScale n)) *
              Real.rpow (blockScale n) (-s) -
            Real.rpow (shannonScale n) (-s)) := by
    funext n
    simp only [shannonLogScale, shannonScale]
    ring
  rw [heq]
  simpa only [sub_zero] using hsub

private theorem tendsto_shannonLogScale_mul_roundRatio_sub_one
    (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ shannonLogScale n *
      (shannonRoundRatio s n - 1)) atTop (𝓝 0) := by
  have hmajor := tendsto_shannonLogScale_mul_rpow_neg s hs
  refine squeeze_zero (fun n ↦ ?_) (fun n ↦ ?_) hmajor
  · exact mul_nonneg (shannonLogScale_pos n).le (sub_nonneg.mpr (by
      have h := ceil_rpow_ratio_bounds s (n + 2) hs (by omega)
      simpa only [shannonRoundRatio, shannonScale, blockScale,
        Nat.cast_add, Nat.cast_ofNat] using h.1))
  · apply mul_le_mul_of_nonneg_left _ (shannonLogScale_pos n).le
    have h := ceil_rpow_ratio_bounds s (n + 2) hs (by omega)
    have h' : shannonRoundRatio s n ≤
        1 + Real.rpow (shannonScale n) (-s) := by
      simpa only [shannonRoundRatio, shannonScale, blockScale,
        Nat.cast_add, Nat.cast_ofNat] using h.2
    linarith

private theorem tendsto_inv_shannonLogScale :
    Tendsto (fun n : ℕ ↦ (shannonLogScale n)⁻¹) atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (Real.tendsto_log_atTop.comp (by
      change Tendsto blockScale atTop atTop
      exact tendsto_blockScale_atTop))

private theorem tendsto_shannonExpansionActual (theta : ShannonData) :
    Tendsto (shannonExpansionActual theta) atTop
      (𝓝 shannonExpansionLimit) := by
  have hR : 0 < theta.R := by
    linarith [theta.R_gt, theta.c_gt_one]
  have hRone : 0 < theta.R - 1 := by
    linarith [theta.R_gt, theta.c_gt_one]
  have hRonec : 0 < theta.R - 1 - theta.c := by
    linarith [theta.R_gt]
  have hc : 0 < theta.c - 1 := by linarith [theta.c_gt_one]
  have hratio0 := tendsto_shannonRoundRatio theta.R hR
  have hratio1 := tendsto_shannonRoundRatio (theta.R - 1) hRone
  have hratio2 := tendsto_shannonRoundRatio
    (theta.R - 1 - theta.c) hRonec
  have hpower : Tendsto
      (fun n : ℕ ↦ Real.rpow (shannonScale n) (1 - theta.c))
      atTop (𝓝 0) := by
    have hbase : Tendsto
        (fun n : ℕ ↦ Real.rpow (shannonScale n) (-(theta.c - 1)))
        atTop (𝓝 0) := by
      exact (tendsto_rpow_neg_atTop hc).comp (by
        change Tendsto blockScale atTop atTop
        exact tendsto_blockScale_atTop)
    simpa only [show 1 - theta.c = -(theta.c - 1) by ring] using hbase
  have hlog0 := tendsto_shannonLogScale_mul_roundRatio_sub_one theta.R hR
  have hlog1 := tendsto_shannonLogScale_mul_roundRatio_sub_one
    (theta.R - 1) hRone
  have hlogPower := tendsto_shannonLogScale_mul_rpow_neg
    (theta.c - 1) hc
  rw [tendsto_pi_nhds]
  intro i
  fin_cases i
  · simpa [shannonExpansionActual, shannonExpansionLimit] using hratio0
  · simpa [shannonExpansionActual, shannonExpansionLimit] using hratio1
  · simpa [shannonExpansionActual, shannonExpansionLimit] using
      hratio2.mul hpower
  · have hdiff := hlog0.sub hlog1
    have heq :
        (fun n : ℕ ↦ shannonLogScale n *
          (shannonRoundRatio theta.R n -
            shannonRoundRatio (theta.R - 1) n)) =
          (fun n : ℕ ↦
            shannonLogScale n * (shannonRoundRatio theta.R n - 1) -
              shannonLogScale n *
                (shannonRoundRatio (theta.R - 1) n - 1)) := by
      funext n
      ring
    have hdiff' : Tendsto
        (fun n : ℕ ↦ shannonLogScale n *
          (shannonRoundRatio theta.R n -
            shannonRoundRatio (theta.R - 1) n)) atTop (𝓝 0) := by
      rw [heq]
      simpa only [sub_zero] using hdiff
    simpa [shannonExpansionActual, shannonExpansionLimit] using hdiff'
  · have hprod := hratio2.mul hlogPower
    have heq :
        (fun n : ℕ ↦ shannonLogScale n *
          (shannonRoundRatio (theta.R - 1 - theta.c) n *
            Real.rpow (shannonScale n) (1 - theta.c))) =
          (fun n : ℕ ↦ shannonRoundRatio (theta.R - 1 - theta.c) n *
            (shannonLogScale n *
              Real.rpow (shannonScale n) (-(theta.c - 1)))) := by
      funext n
      rw [show 1 - theta.c = -(theta.c - 1) by ring]
      ring
    have hprod' : Tendsto
        (fun n : ℕ ↦ shannonLogScale n *
          (shannonRoundRatio (theta.R - 1 - theta.c) n *
            Real.rpow (shannonScale n) (1 - theta.c))) atTop (𝓝 0) := by
      rw [heq]
      simpa only [mul_zero] using hprod
    simpa [shannonExpansionActual, shannonExpansionLimit] using hprod'
  · simpa [shannonExpansionActual, shannonExpansionLimit] using
      tendsto_inv_shannonLogScale

private theorem tendsto_shannonExpansionIdeal :
    Tendsto shannonExpansionIdeal atTop (𝓝 shannonExpansionLimit) := by
  rw [tendsto_pi_nhds]
  intro i
  fin_cases i
  · simp [shannonExpansionIdeal, shannonExpansionLimit]
  · simp [shannonExpansionIdeal, shannonExpansionLimit]
  · simp [shannonExpansionIdeal, shannonExpansionLimit]
  · simp [shannonExpansionIdeal, shannonExpansionLimit]
  · simp [shannonExpansionIdeal, shannonExpansionLimit]
  · simpa [shannonExpansionIdeal, shannonExpansionLimit] using
      tendsto_inv_shannonLogScale

private theorem shannonRoundRatio_mul_rpow (s : ℝ) (n : ℕ) :
    shannonRoundRatio s n * Real.rpow (shannonScale n) s =
      (Nat.ceil (Real.rpow (shannonScale n) s) : ℝ) := by
  unfold shannonRoundRatio
  field_simp [(Real.rpow_pos_of_pos (shannonScale_pos n) s).ne']

private theorem shannonExpansionActual_mass_zero (theta : ShannonData)
    (n : ℕ) :
    Real.rpow (shannonScale n) theta.R *
        (shannonExpansionActual theta n 0) =
      (shannonCount theta n 0 : ℝ) := by
  simp only [shannonExpansionActual, Matrix.cons_val_zero]
  rw [mul_comm]
  exact shannonRoundRatio_mul_rpow theta.R n

private theorem shannonExpansionActual_mass_one (theta : ShannonData)
    (n : ℕ) :
    Real.rpow (shannonScale n) theta.R *
        (shannonExpansionActual theta n 1) =
      (shannonCount theta n 1 : ℝ) * shannonScale n := by
  have hd := shannonScale_pos n
  have hsplit : Real.rpow (shannonScale n) theta.R =
      Real.rpow (shannonScale n) (theta.R - 1) * shannonScale n := by
    calc
      Real.rpow (shannonScale n) theta.R =
          Real.rpow (shannonScale n) ((theta.R - 1) + 1) := by
            congr 1
            ring
      _ = Real.rpow (shannonScale n) (theta.R - 1) *
          Real.rpow (shannonScale n) 1 := by
            change shannonScale n ^ ((theta.R - 1) + 1) =
              shannonScale n ^ (theta.R - 1) *
                shannonScale n ^ (1 : ℝ)
            exact Real.rpow_add hd (theta.R - 1) 1
      _ = _ := by
        change shannonScale n ^ (theta.R - 1) *
          shannonScale n ^ (1 : ℝ) =
            shannonScale n ^ (theta.R - 1) * shannonScale n
        rw [Real.rpow_one]
  simp only [shannonExpansionActual]
  calc
    Real.rpow (shannonScale n) theta.R *
        shannonRoundRatio (theta.R - 1) n =
      shannonRoundRatio (theta.R - 1) n *
        (Real.rpow (shannonScale n) (theta.R - 1) * shannonScale n) := by
          rw [hsplit]
          ring
    _ = (shannonRoundRatio (theta.R - 1) n *
          Real.rpow (shannonScale n) (theta.R - 1)) * shannonScale n := by
          ring
    _ = (shannonCount theta n 1 : ℝ) * shannonScale n := by
          rw [shannonRoundRatio_mul_rpow]
          simp [shannonCount]

private theorem shannonExpansionActual_mass_two (theta : ShannonData)
    (n : ℕ) :
    Real.rpow (shannonScale n) theta.R *
        (shannonExpansionActual theta n 2) =
      (shannonCount theta n 2 : ℝ) * shannonScale n ^ 2 := by
  let s : ℝ := theta.R - 1 - theta.c
  have hd := shannonScale_pos n
  have hsplit : Real.rpow (shannonScale n) theta.R *
      Real.rpow (shannonScale n) (1 - theta.c) =
        Real.rpow (shannonScale n) s * shannonScale n ^ 2 := by
    calc
      Real.rpow (shannonScale n) theta.R *
          Real.rpow (shannonScale n) (1 - theta.c) =
        Real.rpow (shannonScale n) (theta.R + (1 - theta.c)) := by
          change shannonScale n ^ theta.R *
              shannonScale n ^ (1 - theta.c) =
            shannonScale n ^ (theta.R + (1 - theta.c))
          exact (Real.rpow_add hd theta.R (1 - theta.c)).symm
      _ = Real.rpow (shannonScale n) (s + 2) := by
        congr 1
        dsimp only [s]
        ring
      _ = Real.rpow (shannonScale n) s *
          Real.rpow (shannonScale n) (2 : ℝ) := by
        change shannonScale n ^ (s + 2) =
          shannonScale n ^ s * shannonScale n ^ (2 : ℝ)
        exact Real.rpow_add hd s 2
      _ = _ := by
        change shannonScale n ^ s * shannonScale n ^ (2 : ℝ) =
          shannonScale n ^ s * shannonScale n ^ 2
        exact congrArg (fun x : ℝ ↦ shannonScale n ^ s * x)
          (Real.rpow_natCast (shannonScale n) 2)
  simp only [shannonExpansionActual]
  calc
    Real.rpow (shannonScale n) theta.R *
        (shannonRoundRatio s n *
          Real.rpow (shannonScale n) (1 - theta.c)) =
      shannonRoundRatio s n *
        (Real.rpow (shannonScale n) theta.R *
          Real.rpow (shannonScale n) (1 - theta.c)) := by ring
    _ = shannonRoundRatio s n *
        (Real.rpow (shannonScale n) s * shannonScale n ^ 2) := by
          rw [hsplit]
    _ = (shannonRoundRatio s n * Real.rpow (shannonScale n) s) *
        shannonScale n ^ 2 := by ring
    _ = (shannonCount theta n 2 : ℝ) * shannonScale n ^ 2 := by
          rw [shannonRoundRatio_mul_rpow]
          simp [shannonCount, s]

private theorem shannonExpansionActual_factor_zero (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (lambda : ℝ) :
    shannonBase theta n z (shannonRepresentative theta n 0) *
        (1 + shannonBlockVelocity theta n z 0 * lambda) =
      shannonExpansionA theta (shannonExpansionActual theta n) z lambda := by
  have hL := (shannonLogScale_pos n).ne'
  have hq := theta.q_pos.ne'
  simp [shannonBase, shannonRepresentative,
    shannonBlockVelocity_zero, shannonExpansionA,
    shannonExpansionActual]
  field_simp [hL, hq]

private theorem shannonExpansionActual_factor_one (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (lambda : ℝ) :
    shannonBase theta n z (shannonRepresentative theta n 1) *
        (1 + shannonBlockVelocity theta n z 1 * lambda) =
      shannonScale n *
        shannonExpansionB theta (shannonExpansionActual theta n) z lambda := by
  have hL := (shannonLogScale_pos n).ne'
  have hp := theta.p_pos.ne'
  simp [shannonBase, shannonRepresentative,
    shannonBlockVelocity_one, shannonExpansionB,
    shannonExpansionActual]
  field_simp [hL, hp]
  ring

private theorem shannonExpansionActual_factor_two (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (lambda : ℝ) :
    shannonBase theta n z (shannonRepresentative theta n 2) *
        (1 + shannonBlockVelocity theta n z 2 * lambda) =
      shannonScale n ^ 2 *
        shannonExpansionC (shannonExpansionActual theta n) z lambda := by
  simp [shannonBase, shannonRepresentative, shannonExpansionC]

private theorem shannonExpansionActual_total (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (lambda : ℝ) :
    Real.rpow (shannonScale n) theta.R *
        shannonExpansionTotal theta (shannonExpansionActual theta n) z lambda =
      shannonMass theta n z lambda := by
  rw [shannonMass_eq_sum, Fin.sum_univ_three]
  unfold shannonExpansionTotal
  calc
    Real.rpow (shannonScale n) theta.R *
        (shannonExpansionActual theta n 0 *
              shannonExpansionA theta (shannonExpansionActual theta n) z lambda +
            shannonExpansionActual theta n 1 *
              shannonExpansionB theta (shannonExpansionActual theta n) z lambda +
          shannonExpansionActual theta n 2 *
            shannonExpansionC (shannonExpansionActual theta n) z lambda) =
      (Real.rpow (shannonScale n) theta.R *
          shannonExpansionActual theta n 0) *
            shannonExpansionA theta (shannonExpansionActual theta n) z lambda +
        (Real.rpow (shannonScale n) theta.R *
          shannonExpansionActual theta n 1) *
            shannonExpansionB theta (shannonExpansionActual theta n) z lambda +
        (Real.rpow (shannonScale n) theta.R *
          shannonExpansionActual theta n 2) *
            shannonExpansionC (shannonExpansionActual theta n) z lambda := by ring
    _ = (shannonCount theta n 0 : ℝ) *
            shannonExpansionA theta (shannonExpansionActual theta n) z lambda +
          ((shannonCount theta n 1 : ℝ) * shannonScale n) *
            shannonExpansionB theta (shannonExpansionActual theta n) z lambda +
          ((shannonCount theta n 2 : ℝ) * shannonScale n ^ 2) *
            shannonExpansionC (shannonExpansionActual theta n) z lambda := by
      rw [shannonExpansionActual_mass_zero,
        shannonExpansionActual_mass_one, shannonExpansionActual_mass_two]
    _ = (shannonCount theta n 0 : ℝ) *
            shannonExpansionA theta (shannonExpansionActual theta n) z lambda +
          (shannonCount theta n 1 : ℝ) *
            (shannonScale n *
              shannonExpansionB theta (shannonExpansionActual theta n) z lambda) +
          (shannonCount theta n 2 : ℝ) *
            (shannonScale n ^ 2 *
              shannonExpansionC (shannonExpansionActual theta n) z lambda) := by ring
    _ = _ := by
      rw [← shannonExpansionActual_factor_zero theta n z lambda,
        ← shannonExpansionActual_factor_one theta n z lambda,
        ← shannonExpansionActual_factor_two theta n z lambda]
      ring

private theorem shannonExpansionActual_mem_domain (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (lambda : ℝ)
    (hpos : letI := shannonIndexNonempty theta n
      LinePositive (shannonLineData theta n z) lambda) :
    (shannonExpansionActual theta n, z, lambda) ∈
      shannonExpansionDomain theta := by
  letI := shannonIndexNonempty theta n
  have hzeroRaw := hpos (shannonRepresentative theta n 0)
  have honeRaw := hpos (shannonRepresentative theta n 1)
  have htwoRaw := hpos (shannonRepresentative theta n 2)
  have hzero : 0 < shannonExpansionA theta
      (shannonExpansionActual theta n) z lambda := by
    rw [← shannonExpansionActual_factor_zero]
    exact hzeroRaw
  have hone : 0 < shannonExpansionB theta
      (shannonExpansionActual theta n) z lambda := by
    have h := shannonExpansionActual_factor_one theta n z lambda
    have hprod : 0 < shannonScale n *
        shannonExpansionB theta (shannonExpansionActual theta n) z lambda := by
      rw [← h]
      exact honeRaw
    exact pos_of_mul_pos_right hprod (shannonScale_pos n).le
  have htwo : 0 < shannonExpansionC
      (shannonExpansionActual theta n) z lambda := by
    have hprod : 0 < shannonScale n ^ 2 *
        shannonExpansionC (shannonExpansionActual theta n) z lambda := by
      rw [← shannonExpansionActual_factor_two]
      exact htwoRaw
    exact pos_of_mul_pos_right hprod (sq_nonneg (shannonScale n))
  have hmass : 0 < shannonMass theta n z lambda := by
    rw [shannonMass_eq_lineMass]
    exact lineMass_pos _ hpos
  have htotal : 0 < shannonExpansionTotal theta
      (shannonExpansionActual theta n) z lambda := by
    have hprod : 0 < Real.rpow (shannonScale n) theta.R *
        shannonExpansionTotal theta (shannonExpansionActual theta n) z lambda := by
      rw [shannonExpansionActual_total]
      exact hmass
    exact pos_of_mul_pos_right hprod
      (Real.rpow_pos_of_pos (shannonScale_pos n) theta.R).le
  exact ⟨hzero, hone, htwo, htotal⟩

private theorem shannonExpansionIdeal_mem_domain (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (lambda : ℝ)
    (hpos : letI := shannonIndexNonempty theta n
      LinePositive (shannonLineData theta n z) lambda) :
    (shannonExpansionIdeal n, z, lambda) ∈
      shannonExpansionDomain theta := by
  letI := shannonIndexNonempty theta n
  have hzero := (shannonExpansionActual_mem_domain theta n z lambda hpos).1
  have hone := (shannonExpansionActual_mem_domain theta n z lambda hpos).2.1
  have htwo := (shannonExpansionActual_mem_domain theta n z lambda hpos).2.2.1
  have hpq : theta.q + theta.p = 1 := by simp [ShannonData.q]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [shannonExpansionA, shannonExpansionActual,
      shannonExpansionIdeal] using hzero
  · simpa [shannonExpansionB, shannonExpansionActual,
      shannonExpansionIdeal] using hone
  · simpa [shannonExpansionC] using htwo
  · simp [shannonExpansionTotal, shannonExpansionA, shannonExpansionB,
      shannonExpansionC, shannonExpansionIdeal, hpq]

private theorem shannonExpansionLimit_mem_domain (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (lambda : ℝ)
    (hpos : letI := shannonIndexNonempty theta n
      LinePositive (shannonLineData theta n z) lambda) :
    (shannonExpansionLimit, z, lambda) ∈ shannonExpansionDomain theta := by
  have hpq : theta.q + theta.p = 1 := by simp [ShannonData.q]
  have htwo :=
    (shannonExpansionActual_mem_domain theta n z lambda hpos).2.2.1
  exact ⟨by simpa [shannonExpansionA, shannonExpansionLimit] using theta.q_pos,
    by simpa [shannonExpansionB, shannonExpansionLimit] using theta.p_pos,
    by simpa [shannonExpansionC] using htwo,
     by simp [shannonExpansionTotal, shannonExpansionA, shannonExpansionB,
       shannonExpansionC, shannonExpansionLimit, hpq]⟩

@[simp] private theorem shannonExpansionIdeal_model (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (lambda : ℝ) :
    shannonExpansionModel theta (shannonExpansionIdeal n, z, lambda) = 0 := by
  have hpq : theta.q + theta.p = 1 := by
    simp [ShannonData.q]
  simp [shannonExpansionModel, shannonExpansionIdeal,
    shannonExpansionTotal, shannonExpansionA, shannonExpansionB,
    shannonExpansionC, hpq]

@[simp] private theorem shannonExpansionLimit_model (theta : ShannonData)
    (z : ℝ × ℝ) (lambda : ℝ) :
    shannonExpansionModel theta (shannonExpansionLimit, z, lambda) = 0 := by
  have hpq : theta.q + theta.p = 1 := by
    simp [ShannonData.q]
  simp [shannonExpansionModel, shannonExpansionLimit,
    shannonExpansionTotal, shannonExpansionA, shannonExpansionB,
    shannonExpansionC, hpq]

/-- Sum of raw-coordinate logarithmic moments, reduced to the three blocks. -/
private def shannonRawLogSum (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (lambda : ℝ) : ℝ :=
  ∑ j : Fin 3, (shannonCount theta n j : ℝ) *
    (shannonBase theta n z (shannonRepresentative theta n j) *
      (1 + shannonBlockVelocity theta n z j * lambda)) *
    Real.log (shannonBase theta n z (shannonRepresentative theta n j) *
      (1 + shannonBlockVelocity theta n z j * lambda))

private theorem entropyLine_one_eq_logMass_sub (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (lambda : ℝ)
    (hpos : letI := shannonIndexNonempty theta n
      LinePositive (shannonLineData theta n z) lambda) :
    letI := shannonIndexNonempty theta n
    entropyLine (shannonLineData theta n z) 1 lambda =
      Real.log (shannonMass theta n z lambda) -
        shannonRawLogSum theta n z lambda /
          shannonMass theta n z lambda := by
  letI := shannonIndexNonempty theta n
  let L := shannonLineData theta n z
  have hmass : 0 < lineMass L lambda := lineMass_pos L hpos
  have hsum : ∑ i, lineRaw L lambda i / lineMass L lambda = 1 := by
    simpa only [lineProb_apply_of_positive L hpos, l1Mass] using
      (lineProb L lambda).2.2
  have hraw : (∑ i : ShannonIndex theta n,
      lineRaw L lambda i * Real.log (lineRaw L lambda i)) =
      shannonRawLogSum theta n z lambda := by
    change (∑ i : Σ j : Fin 3, Fin (shannonCount theta n j),
      lineRaw L lambda i * Real.log (lineRaw L lambda i)) = _
    rw [Fintype.sum_sigma]
    unfold shannonRawLogSum
    apply Finset.sum_congr rfl
    intro j _hj
    change (∑ _i : Fin (shannonCount theta n j),
      (shannonBase theta n z (shannonRepresentative theta n j) *
        (1 + shannonBlockVelocity theta n z j * lambda)) *
        Real.log (shannonBase theta n z (shannonRepresentative theta n j) *
          (1 + shannonBlockVelocity theta n z j * lambda))) = _
    simp
    ring
  have hprob : (lineProb L lambda).1 =
      (fun i ↦ lineRaw L lambda i / lineMass L lambda) := by
    funext i
    exact lineProb_apply_of_positive L hpos i
  have hlog (i : ShannonIndex theta n) :
      Real.log (lineRaw L lambda i / lineMass L lambda) =
        Real.log (lineRaw L lambda i) - Real.log (lineMass L lambda) :=
    Real.log_div (hpos i).ne' hmass.ne'
  rw [entropyLine, renyi_at_one]
  unfold renyiOne
  rw [hprob]
  simp_rw [hlog, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  have hfirst :
      (∑ x, lineRaw L lambda x / lineMass L lambda *
          Real.log (lineRaw L lambda x)) =
        (∑ x, lineRaw L lambda x * Real.log (lineRaw L lambda x)) /
          lineMass L lambda := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  rw [hfirst, hraw]
  simp only [L, shannonMass_eq_lineMass]
  ring

private theorem shannonError_eq_expansionModel (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (lambda : ℝ)
    (hpos : letI := shannonIndexNonempty theta n
      LinePositive (shannonLineData theta n z) lambda) :
    shannonError theta n z lambda =
      shannonExpansionModel theta
        (shannonExpansionActual theta n, z, lambda) := by
  letI := shannonIndexNonempty theta n
  let xi := shannonExpansionActual theta n
  let d := shannonScale n
  let L := shannonLogScale n
  let D := Real.rpow d theta.R
  let a := shannonExpansionA theta xi z lambda
  let b := shannonExpansionB theta xi z lambda
  let c := shannonExpansionC xi z lambda
  let T := shannonExpansionTotal theta xi z lambda
  have hdomain := shannonExpansionActual_mem_domain theta n z lambda hpos
  have hb : 0 < b := hdomain.2.1
  have hc : 0 < c := hdomain.2.2.1
  have hT : 0 < T := hdomain.2.2.2
  have hd : 0 < d := shannonScale_pos n
  have hL : 0 < L := shannonLogScale_pos n
  have hD : 0 < D := Real.rpow_pos_of_pos hd theta.R
  have hx0 : D * xi 0 = (shannonCount theta n 0 : ℝ) := by
    simpa only [D, xi, d] using shannonExpansionActual_mass_zero theta n
  have hx1 : D * xi 1 =
      (shannonCount theta n 1 : ℝ) * d := by
    simpa only [D, xi, d] using shannonExpansionActual_mass_one theta n
  have hx2 : D * xi 2 =
      (shannonCount theta n 2 : ℝ) * d ^ 2 := by
    simpa only [D, xi, d] using shannonExpansionActual_mass_two theta n
  have hfactor0 : shannonBase theta n z (shannonRepresentative theta n 0) *
      (1 + shannonBlockVelocity theta n z 0 * lambda) = a := by
    simpa only [a, xi] using
      shannonExpansionActual_factor_zero theta n z lambda
  have hfactor1 : shannonBase theta n z (shannonRepresentative theta n 1) *
      (1 + shannonBlockVelocity theta n z 1 * lambda) = d * b := by
    simpa only [b, d, xi] using
      shannonExpansionActual_factor_one theta n z lambda
  have hfactor2 : shannonBase theta n z (shannonRepresentative theta n 2) *
      (1 + shannonBlockVelocity theta n z 2 * lambda) = d ^ 2 * c := by
    simpa only [c, d, xi] using
      shannonExpansionActual_factor_two theta n z lambda
  have hlogD : Real.log D = theta.R * L := by
    dsimp only [D, L, d, shannonLogScale]
    rw [Real.rpow_eq_pow, Real.log_rpow (shannonScale_pos n)]
  have hlogdb : Real.log (d * b) = L + Real.log b := by
    rw [Real.log_mul hd.ne' hb.ne']
    rfl
  have hlogd2c : Real.log (d ^ 2 * c) = 2 * L + Real.log c := by
    rw [Real.log_mul (pow_pos hd 2).ne' hc.ne', Real.log_pow]
    rfl
  have hmass : shannonMass theta n z lambda = D * T := by
    symm
    simpa only [D, T, d, xi] using
      shannonExpansionActual_total theta n z lambda
  have hlogMass : Real.log (shannonMass theta n z lambda) =
      theta.R * L + Real.log T := by
    rw [hmass, Real.log_mul hD.ne' hT.ne', hlogD]
  have hraw : shannonRawLogSum theta n z lambda =
      D * (xi 0 * a * Real.log a +
        xi 1 * b * (L + Real.log b) +
        xi 2 * c * (2 * L + Real.log c)) := by
    have hy1 : (shannonCount theta n 1 : ℝ) * (d * b) =
        D * xi 1 * b := by
      calc
        (shannonCount theta n 1 : ℝ) * (d * b) =
            ((shannonCount theta n 1 : ℝ) * d) * b := by ring
        _ = (D * xi 1) * b := by rw [← hx1]
    have hy2 : (shannonCount theta n 2 : ℝ) * (d ^ 2 * c) =
        D * xi 2 * c := by
      calc
        (shannonCount theta n 2 : ℝ) * (d ^ 2 * c) =
            ((shannonCount theta n 2 : ℝ) * d ^ 2) * c := by ring
        _ = (D * xi 2) * c := by rw [← hx2]
    unfold shannonRawLogSum
    rw [Fin.sum_univ_three, hfactor0, hfactor1, hfactor2,
      hlogdb, hlogd2c, ← hx0, hy1, hy2]
    ring
  rw [shannonError, entropyLine_one_eq_logMass_sub theta n z lambda hpos,
    hlogMass, hraw, hmass]
  unfold shannonExpansionModel shannonMain
  have hpq : theta.q + theta.p = 1 := by simp [ShannonData.q]
  have hxi3 : xi 3 = L * (xi 0 - xi 1) := by
    simp [xi, L, shannonExpansionActual]
  have hxi4 : xi 4 = L * xi 2 := by
    simp [xi, L, shannonExpansionActual]
  have hxi5 : xi 5 = L⁻¹ := by
    simp [xi, L, shannonExpansionActual]
  have haFormula : a = theta.q + z.1 * lambda / L := by
    dsimp only [a]
    unfold shannonExpansionA
    rw [hxi5]
    field_simp [hL.ne']
  have hbFormula : b = theta.p - z.1 * lambda / L := by
    dsimp only [b]
    unfold shannonExpansionB
    rw [hxi5]
    field_simp [hL.ne']
  have hab : a + b = 1 := by
    rw [haFormula, hbFormula]
    linarith [hpq]
  have hbEq : b = 1 - a := by linarith [hab]
  have hk : z.1 * lambda / L = a - theta.q := by
    linarith [haFormula]
  have hTdef : T = xi 0 * a + xi 1 * b + xi 2 * c := by
    rfl
  have hcoefficient :
      theta.R - theta.p + (a - theta.q) = theta.R - b := by
    linarith [hpq, hab]
  have hmainFormula :
      (theta.R - theta.p + z.1 * lambda / L) * L -
          (theta.q + z.1 * lambda / L) *
            Real.log (theta.q + z.1 * lambda / L) -
          (theta.p - z.1 * lambda / L) *
            Real.log (theta.p - z.1 * lambda / L) =
        (theta.R - b) * L - a * Real.log a - b * Real.log b := by
    rw [← haFormula, ← hbFormula, hk, hcoefficient]
  have hrawSplit :
      xi 0 * a * Real.log a +
          xi 1 * b * (L + Real.log b) +
          xi 2 * c * (2 * L + Real.log c) =
        (xi 0 * a * Real.log a + xi 1 * b * Real.log b +
            xi 2 * c * Real.log c) +
          L * (xi 1 * b + 2 * xi 2 * c) := by
    ring
  have hrawQuotient :
      D * (xi 0 * a * Real.log a +
          xi 1 * b * (L + Real.log b) +
          xi 2 * c * (2 * L + Real.log c)) / (D * T) =
        (xi 0 * a * Real.log a + xi 1 * b * Real.log b +
            xi 2 * c * Real.log c) / T +
          L * (xi 1 * b + 2 * xi 2 * c) / T := by
    rw [hrawSplit]
    field_simp [hD.ne', hT.ne']
  have hscaleTerm :
      b * L - L * (xi 1 * b + 2 * xi 2 * c) / T =
        (a * b * xi 3 + c * (b - 2) * xi 4) / T := by
    rw [hxi3, hxi4]
    have hnum :
        b * T - (xi 1 * b + 2 * xi 2 * c) =
          a * b * (xi 0 - xi 1) + c * (b - 2) * xi 2 := by
      rw [hTdef, hbEq]
      ring
    calc
      b * L - L * (xi 1 * b + 2 * xi 2 * c) / T =
          L * (b * T - (xi 1 * b + 2 * xi 2 * c)) / T := by
        field_simp [hT.ne']
      _ = L * (a * b * (xi 0 - xi 1) + c * (b - 2) * xi 2) / T := by
        rw [hnum]
      _ = (a * b * (L * (xi 0 - xi 1)) +
          c * (b - 2) * (L * xi 2)) / T := by ring
  change
    theta.R * L + Real.log T -
          D * (xi 0 * a * Real.log a +
            xi 1 * b * (L + Real.log b) +
            xi 2 * c * (2 * L + Real.log c)) / (D * T) -
        ((theta.R - theta.p + z.1 * lambda / L) * L -
          (theta.q + z.1 * lambda / L) *
            Real.log (theta.q + z.1 * lambda / L) -
          (theta.p - z.1 * lambda / L) *
            Real.log (theta.p - z.1 * lambda / L)) =
      Real.log T + (a * b * xi 3 + c * (b - 2) * xi 4) / T -
          (xi 0 * a * Real.log a + xi 1 * b * Real.log b +
            xi 2 * c * Real.log c) / T +
        a * Real.log a + b * Real.log b
  calc
    _ = Real.log T +
          (b * L - L * (xi 1 * b + 2 * xi 2 * c) / T) -
          (xi 0 * a * Real.log a + xi 1 * b * Real.log b +
            xi 2 * c * Real.log c) / T +
          a * Real.log a + b * Real.log b := by
      rw [hrawQuotient, hmainFormula]
      ring
    _ = _ := by rw [hscaleTerm]

/-! ## Continuous lambda jets of the normalized model -/

abbrev ShannonExpansionSpace :=
  ShannonExpansionCoeffs × ((ℝ × ℝ) × ℝ)

def shannonExpansionLambdaDirection : ShannonExpansionSpace :=
  (0, ((0, 0), 1))

def shannonExpansionFirst (theta : ShannonData)
    (x : ShannonExpansionSpace) : ℝ :=
  fderiv ℝ (shannonExpansionModel theta) x
    shannonExpansionLambdaDirection

def shannonExpansionSecond (theta : ShannonData)
    (x : ShannonExpansionSpace) : ℝ :=
  fderiv ℝ (shannonExpansionFirst theta) x
    shannonExpansionLambdaDirection

def shannonExpansionJet (theta : ShannonData) (j : ℕ)
    (x : ShannonExpansionSpace) : ℝ :=
  match j with
  | 0 => shannonExpansionModel theta x
  | 1 => shannonExpansionFirst theta x
  | 2 => shannonExpansionSecond theta x
  | _ => 0

private theorem contDiffOn_shannonExpansionFirst (theta : ShannonData) :
    ContDiffOn ℝ 1 (shannonExpansionFirst theta)
      (shannonExpansionDomain theta) := by
  have hDf : ContDiffOn ℝ 1 (fderiv ℝ (shannonExpansionModel theta))
      (shannonExpansionDomain theta) :=
    (contDiffOn_shannonExpansionModel theta).fderiv_of_isOpen
      (isOpen_shannonExpansionDomain theta) (m := 1) (by simp)
  unfold shannonExpansionFirst
  exact hDf.clm_apply contDiffOn_const

private theorem contDiffOn_shannonExpansionSecond (theta : ShannonData) :
    ContDiffOn ℝ 0 (shannonExpansionSecond theta)
      (shannonExpansionDomain theta) := by
  have hDf : ContDiffOn ℝ 0 (fderiv ℝ (shannonExpansionFirst theta))
      (shannonExpansionDomain theta) :=
    (contDiffOn_shannonExpansionFirst theta).fderiv_of_isOpen
      (isOpen_shannonExpansionDomain theta) (m := 0) (by simp)
  unfold shannonExpansionSecond
  exact hDf.clm_apply contDiffOn_const

private theorem continuousOn_shannonExpansionJet (theta : ShannonData)
    (j : ℕ) (hj : j ≤ 2) :
    ContinuousOn (shannonExpansionJet theta j)
      (shannonExpansionDomain theta) := by
  interval_cases j
  · change ContinuousOn (shannonExpansionModel theta) _
    exact (contDiffOn_shannonExpansionModel theta).continuousOn
  · change ContinuousOn (shannonExpansionFirst theta) _
    exact (contDiffOn_shannonExpansionFirst theta).continuousOn
  · change ContinuousOn (shannonExpansionSecond theta) _
    exact (contDiffOn_shannonExpansionSecond theta).continuousOn

private theorem hasDerivAt_shannonExpansionInsert
    (xi : ShannonExpansionCoeffs) (z : ℝ × ℝ) (lambda : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (xi, (z, t)))
      shannonExpansionLambdaDirection lambda := by
  have h := (hasDerivAt_const lambda xi).prodMk
    ((hasDerivAt_const lambda z).prodMk (hasDerivAt_id lambda))
  apply h.congr_deriv
  ext <;> simp [shannonExpansionLambdaDirection]

private theorem shannonExpansion_section_jet (theta : ShannonData)
    (xi : ShannonExpansionCoeffs) (z : ℝ × ℝ) (lambda : ℝ)
    (hmem : (xi, z, lambda) ∈ shannonExpansionDomain theta)
    (j : ℕ) (hj : j ≤ 2) :
    iteratedDeriv
        (fun t ↦ shannonExpansionModel theta (xi, z, t)) j lambda =
      shannonExpansionJet theta j (xi, z, lambda) := by
  have hFdiff : DifferentiableOn ℝ (shannonExpansionModel theta)
      (shannonExpansionDomain theta) :=
    (contDiffOn_shannonExpansionModel theta).differentiableOn (by simp)
  have hFirstDiff : DifferentiableOn ℝ (shannonExpansionFirst theta)
      (shannonExpansionDomain theta) :=
    (contDiffOn_shannonExpansionFirst theta).differentiableOn_one
  have hline := hasDerivAt_shannonExpansionInsert xi z lambda
  have hFAt : HasFDerivAt (shannonExpansionModel theta)
      (fderiv ℝ (shannonExpansionModel theta) (xi, z, lambda))
      (xi, z, lambda) :=
    ((hFdiff _ hmem).differentiableAt
      ((isOpen_shannonExpansionDomain theta).mem_nhds hmem)).hasFDerivAt
  have hFirstAt : HasFDerivAt (shannonExpansionFirst theta)
      (fderiv ℝ (shannonExpansionFirst theta) (xi, z, lambda))
      (xi, z, lambda) :=
    ((hFirstDiff _ hmem).differentiableAt
      ((isOpen_shannonExpansionDomain theta).mem_nhds hmem)).hasFDerivAt
  interval_cases j
  · rfl
  · change deriv
      (fun t ↦ shannonExpansionModel theta (xi, z, t)) lambda = _
    exact (hFAt.comp_hasDerivAt lambda hline).deriv
  · change deriv (deriv
      (fun t ↦ shannonExpansionModel theta (xi, z, t))) lambda = _
    have hlineNhd :
        {t : ℝ | (xi, z, t) ∈ shannonExpansionDomain theta} ∈ 𝓝 lambda := by
      exact ((isOpen_shannonExpansionDomain theta).preimage
        (by fun_prop)).mem_nhds hmem
    have hfirstEvent : deriv
        (fun t ↦ shannonExpansionModel theta (xi, z, t)) =ᶠ[𝓝 lambda]
        (fun t ↦ shannonExpansionFirst theta (xi, z, t)) := by
      filter_upwards [hlineNhd] with t ht
      have hFt : HasFDerivAt (shannonExpansionModel theta)
          (fderiv ℝ (shannonExpansionModel theta) (xi, z, t))
          (xi, z, t) :=
        ((hFdiff _ ht).differentiableAt
          ((isOpen_shannonExpansionDomain theta).mem_nhds ht)).hasFDerivAt
      exact (hFt.comp_hasDerivAt t
        (hasDerivAt_shannonExpansionInsert xi z t)).deriv
    rw [Filter.EventuallyEq.deriv_eq hfirstEvent]
    exact (hFirstAt.comp_hasDerivAt lambda hline).deriv

private theorem iteratedDeriv_eq_of_eqOn_open_two
    {f g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U)
    (hfg : Set.EqOn f g U) (j : ℕ) (hj : j ≤ 2) :
    iteratedDeriv f j x = iteratedDeriv g j x := by
  interval_cases j
  · simp only [iteratedDeriv_zero]
    exact hfg hx
  · change deriv f x = deriv g x
    exact Filter.EventuallyEq.deriv_eq
      (eventuallyEq_of_mem (hU.mem_nhds hx) hfg)
  · change deriv (deriv f) x = deriv (deriv g) x
    have hderiv : deriv f =ᶠ[𝓝 x] deriv g := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact Filter.EventuallyEq.deriv_eq
        (eventuallyEq_of_mem (hU.mem_nhds hy) hfg)
    exact Filter.EventuallyEq.deriv_eq hderiv

private theorem shannonExpansionIdeal_jet_zero (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (lambda : ℝ)
    (hmem : (shannonExpansionIdeal n, z, lambda) ∈
      shannonExpansionDomain theta)
    (j : ℕ) (hj : j ≤ 2) :
    shannonExpansionJet theta j (shannonExpansionIdeal n, z, lambda) = 0 := by
  rw [← shannonExpansion_section_jet theta
    (shannonExpansionIdeal n) z lambda hmem j hj]
  interval_cases j <;>
    simp [iteratedDeriv, shannonExpansionIdeal_model]

private theorem shannonError_jet_eq (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hpos : letI := shannonIndexNonempty theta n
      ∀ lambda ∈ Icc (-epsilon) epsilon,
        LinePositive (shannonLineData theta n z) lambda)
    (lambda : ℝ) (hlambda : lambda ∈ Icc (-epsilon / 2) (epsilon / 2))
    (j : ℕ) (hj : j ≤ 2) :
    iteratedDeriv (shannonError theta n z) j lambda =
      shannonExpansionJet theta j
        (shannonExpansionActual theta n, z, lambda) := by
  letI := shannonIndexNonempty theta n
  have hlambdaOpen : lambda ∈ Ioo (-epsilon) epsilon := by
    constructor <;> linarith [hlambda.1, hlambda.2, hepsilon]
  have hEq : Set.EqOn (shannonError theta n z)
      (fun t ↦ shannonExpansionModel theta
        (shannonExpansionActual theta n, z, t))
      (Ioo (-epsilon) epsilon) := by
    intro t ht
    exact shannonError_eq_expansionModel theta n z t
      (hpos t ⟨ht.1.le, ht.2.le⟩)
  rw [iteratedDeriv_eq_of_eqOn_open_two isOpen_Ioo hlambdaOpen hEq j hj]
  exact shannonExpansion_section_jet theta
    (shannonExpansionActual theta n) z lambda
    (shannonExpansionActual_mem_domain theta n z lambda
      (hpos lambda ⟨hlambdaOpen.1.le, hlambdaOpen.2.le⟩)) j hj

private def shannonExpansionCoeffCompact (theta : ShannonData) :
    Set ShannonExpansionCoeffs :=
  insert shannonExpansionLimit (range (shannonExpansionActual theta)) ∪
    insert shannonExpansionLimit (range shannonExpansionIdeal)

private theorem isCompact_shannonExpansionCoeffCompact
    (theta : ShannonData) :
    IsCompact (shannonExpansionCoeffCompact theta) := by
  unfold shannonExpansionCoeffCompact
  exact (tendsto_shannonExpansionActual theta).isCompact_insert_range.union
    tendsto_shannonExpansionIdeal.isCompact_insert_range

private theorem shannonExpansionActual_mem_coeffCompact
    (theta : ShannonData) (n : ℕ) :
    shannonExpansionActual theta n ∈
      shannonExpansionCoeffCompact theta := by
  exact Or.inl (mem_insert_iff.mpr (Or.inr ⟨n, rfl⟩))

private theorem shannonExpansionIdeal_mem_coeffCompact
    (theta : ShannonData) (n : ℕ) :
    shannonExpansionIdeal n ∈ shannonExpansionCoeffCompact theta := by
  exact Or.inr (mem_insert_iff.mpr (Or.inr ⟨n, rfl⟩))

private theorem shannonExpansionLimit_mem_coeffCompact
    (theta : ShannonData) :
    shannonExpansionLimit ∈ shannonExpansionCoeffCompact theta := by
  exact Or.inl (mem_insert_iff.mpr (Or.inl rfl))

private def shannonExpansionJetUniformError (theta : ShannonData)
    (K : Set (ℝ × ℝ)) (lambda0 : ℝ) (j n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ z ∈ K, ∃ lambda ∈ Icc (-lambda0) lambda0,
    r = |shannonExpansionJet theta j
          (shannonExpansionActual theta n, z, lambda) -
        shannonExpansionJet theta j
          (shannonExpansionIdeal n, z, lambda)|}

private theorem tendsto_shannonExpansionJetUniformError
    (theta : ShannonData) (K : Set (ℝ × ℝ))
    (hK : IsCompact K) (hK0 : K.Nonempty)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hpos : ∀ (n : ℕ) (z : ℝ × ℝ), z ∈ K →
      letI := shannonIndexNonempty theta n
      ∀ lambda ∈ Icc (-epsilon) epsilon,
        LinePositive (shannonLineData theta n z) lambda)
    (j : ℕ) (hj : j ≤ 2) :
    Tendsto (fun n ↦ shannonExpansionJetUniformError theta K
      (epsilon / 2) j n) atTop (𝓝 0) := by
  let P : Set ShannonExpansionCoeffs := shannonExpansionCoeffCompact theta
  let Q : Set ((ℝ × ℝ) × ℝ) := K ×ˢ Icc (-(epsilon / 2)) (epsilon / 2)
  let S : Set ShannonExpansionSpace := P ×ˢ Q
  have hP : IsCompact P := isCompact_shannonExpansionCoeffCompact theta
  have hQ : IsCompact Q := hK.prod isCompact_Icc
  have hS : IsCompact S := hP.prod hQ
  have hsubset : S ⊆ shannonExpansionDomain theta := by
    rintro ⟨xi, z, lambda⟩ ⟨hxi, hz, hlambda⟩
    have hlambdaOuter : lambda ∈ Icc (-epsilon) epsilon := by
      constructor <;> linarith [hlambda.1, hlambda.2, hepsilon]
    rcases hxi with hxi | hxi
    · rcases (mem_insert_iff.mp hxi) with rfl | ⟨n, rfl⟩
      · exact shannonExpansionLimit_mem_domain theta 0 z lambda
          (hpos 0 z hz lambda hlambdaOuter)
      · exact shannonExpansionActual_mem_domain theta n z lambda
          (hpos n z hz lambda hlambdaOuter)
    · rcases (mem_insert_iff.mp hxi) with rfl | ⟨n, rfl⟩
      · exact shannonExpansionLimit_mem_domain theta 0 z lambda
          (hpos 0 z hz lambda hlambdaOuter)
      · exact shannonExpansionIdeal_mem_domain theta n z lambda
          (hpos n z hz lambda hlambdaOuter)
  have hcontinuous : ContinuousOn (shannonExpansionJet theta j) S :=
    (continuousOn_shannonExpansionJet theta j hj).mono hsubset
  have huniform : UniformContinuousOn (shannonExpansionJet theta j) S :=
    hS.uniformContinuousOn_of_continuous hcontinuous
  have hdist : Tendsto (fun n ↦ dist (shannonExpansionActual theta n)
      (shannonExpansionIdeal n)) atTop (𝓝 0) := by
    simpa only [dist_self] using
      (tendsto_shannonExpansionActual theta).dist
        tendsto_shannonExpansionIdeal
  rw [Metric.tendsto_nhds]
  intro eta heta
  obtain ⟨delta, hdelta, hdeltaControl⟩ :=
    (Metric.uniformContinuousOn_iff.mp huniform) (eta / 2) (half_pos heta)
  have hevent : ∀ᶠ n in atTop,
      dist (shannonExpansionActual theta n) (shannonExpansionIdeal n) <
        delta := by
    filter_upwards [hdist.eventually (Metric.ball_mem_nhds 0 hdelta)] with n hn
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (dist_nonneg : 0 ≤ dist
        (shannonExpansionActual theta n) (shannonExpansionIdeal n))] using hn
  filter_upwards [hevent] with n hn
  have hpoint : ∀ z ∈ K, ∀ lambda ∈ Icc (-(epsilon / 2)) (epsilon / 2),
      |shannonExpansionJet theta j
          (shannonExpansionActual theta n, z, lambda) -
        shannonExpansionJet theta j
          (shannonExpansionIdeal n, z, lambda)| < eta / 2 := by
    intro z hz lambda hlambda
    have hx : (shannonExpansionActual theta n, z, lambda) ∈ S :=
      ⟨shannonExpansionActual_mem_coeffCompact theta n, hz, hlambda⟩
    have hy : (shannonExpansionIdeal n, z, lambda) ∈ S :=
      ⟨shannonExpansionIdeal_mem_coeffCompact theta n, hz, hlambda⟩
    have hinput : dist
        (shannonExpansionActual theta n, (z, lambda))
        (shannonExpansionIdeal n, (z, lambda)) < delta := by
      simpa only [dist_prod_same_right] using hn
    have hout := hdeltaControl
      (x := (shannonExpansionActual theta n, z, lambda)) hx
      (y := (shannonExpansionIdeal n, z, lambda)) hy hinput
    simpa only [Real.dist_eq] using hout
  let E : Set ℝ := {r : ℝ | ∃ z ∈ K,
    ∃ lambda ∈ Icc (-(epsilon / 2)) (epsilon / 2),
      r = |shannonExpansionJet theta j
          (shannonExpansionActual theta n, z, lambda) -
        shannonExpansionJet theta j
          (shannonExpansionIdeal n, z, lambda)|}
  obtain ⟨z0, hz0⟩ := hK0
  have hlambda0 : (0 : ℝ) ∈ Icc (-(epsilon / 2)) (epsilon / 2) := by
    constructor <;> linarith [hepsilon]
  have hE0 : |shannonExpansionJet theta j
      (shannonExpansionActual theta n, z0, 0) -
    shannonExpansionJet theta j
      (shannonExpansionIdeal n, z0, 0)| ∈ E :=
    ⟨z0, hz0, 0, hlambda0, rfl⟩
  have hEbdd : BddAbove E := by
    refine ⟨eta / 2, ?_⟩
    intro r hr
    rcases hr with ⟨z, hz, lambda, hlambda, rfl⟩
    exact (hpoint z hz lambda hlambda).le
  have hnonneg : 0 ≤ sSup E :=
    (abs_nonneg _).trans (le_csSup hEbdd hE0)
  have hupper : sSup E ≤ eta / 2 := by
    apply csSup_le
    · exact ⟨_, hE0⟩
    · intro r hr
      rcases hr with ⟨z, hz, lambda, hlambda, rfl⟩
      exact (hpoint z hz lambda hlambda).le
  change dist (shannonExpansionJetUniformError theta K
    (epsilon / 2) j n) 0 < eta
  rw [Real.dist_eq, sub_zero, abs_of_nonneg]
  · exact hupper.trans_lt (half_lt_self heta)
  · simpa only [shannonExpansionJetUniformError, E] using hnonneg

private theorem shannonCtwoError_eq_jetUniformError
    (theta : ShannonData) (K : Set (ℝ × ℝ))
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hpos : ∀ (n : ℕ) (z : ℝ × ℝ), z ∈ K →
      letI := shannonIndexNonempty theta n
      ∀ lambda ∈ Icc (-epsilon) epsilon,
        LinePositive (shannonLineData theta n z) lambda)
    (j : ℕ) (hj : j ≤ 2) (n : ℕ) :
    shannonCtwoError theta K (epsilon / 2) j n =
      shannonExpansionJetUniformError theta K (epsilon / 2) j n := by
  unfold shannonCtwoError shannonExpansionJetUniformError
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨z, hz, lambda, hlambda, rfl⟩
    refine ⟨z, hz, lambda, hlambda, ?_⟩
    rw [shannonError_jet_eq theta n z epsilon hepsilon
      (hpos n z hz) lambda (by simpa only [neg_div] using hlambda) j hj,
      shannonExpansionIdeal_jet_zero theta n z lambda
        (shannonExpansionIdeal_mem_domain theta n z lambda
          (hpos n z hz lambda (by
            constructor <;> linarith [hlambda.1, hlambda.2, hepsilon]))) j hj,
      sub_zero]
  · rintro ⟨z, hz, lambda, hlambda, rfl⟩
    refine ⟨z, hz, lambda, hlambda, ?_⟩
    rw [shannonError_jet_eq theta n z epsilon hepsilon
      (hpos n z hz) lambda (by simpa only [neg_div] using hlambda) j hj,
      shannonExpansionIdeal_jet_zero theta n z lambda
        (shannonExpansionIdeal_mem_domain theta n z lambda
          (hpos n z hz lambda (by
            constructor <;> linarith [hlambda.1, hlambda.2, hepsilon]))) j hj,
      sub_zero]

/-! ## The two explicit derivatives of the main term -/

private def shannonMainFirstFormula (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) (lambda : ℝ) : ℝ :=
  let k := z.1 / shannonLogScale n
  let a := theta.q + k * lambda
  let b := theta.p - k * lambda
  z.1 - k * (Real.log a + 1) + k * (Real.log b + 1)

private theorem hasDerivAt_shannonMain (theta : ShannonData) (n : ℕ)
    (z : ℝ × ℝ) {lambda : ℝ}
    (ha : 0 < theta.q + z.1 / shannonLogScale n * lambda)
    (hb : 0 < theta.p - z.1 / shannonLogScale n * lambda) :
    HasDerivAt (shannonMain theta n z)
      (shannonMainFirstFormula theta n z lambda) lambda := by
  let k := z.1 / shannonLogScale n
  let a : ℝ → ℝ := fun t ↦ theta.q + k * t
  let b : ℝ → ℝ := fun t ↦ theta.p - k * t
  have ha' : HasDerivAt a k lambda := by
    simpa only [a, id_eq, mul_one] using
      ((hasDerivAt_id lambda).const_mul k).const_add theta.q
  have hb' : HasDerivAt b (-k) lambda := by
    simpa only [b, id_eq, mul_one] using
      ((hasDerivAt_id lambda).const_mul k).const_sub theta.p
  have ha0 : a lambda ≠ 0 := by simpa only [a, k] using ha.ne'
  have hb0 : b lambda ≠ 0 := by simpa only [b, k] using hb.ne'
  have hlinear0 : HasDerivAt
      (fun t ↦ theta.R - theta.p + k * t) k lambda := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id lambda).const_mul k).const_add (theta.R - theta.p)
  have hkL : k * shannonLogScale n = z.1 := by
    dsimp only [k]
    field_simp [(shannonLogScale_pos n).ne']
  have hlinear : HasDerivAt
      (fun t ↦ (theta.R - theta.p + k * t) * shannonLogScale n)
      z.1 lambda :=
    (hlinear0.mul_const (shannonLogScale n)).congr_deriv hkL
  have halog := ha'.mul (ha'.log ha0)
  have hblog := hb'.mul (hb'.log hb0)
  have h := (hlinear.sub halog).sub hblog
  have heq : shannonMain theta n z =ᶠ[𝓝 lambda]
      (fun t ↦ (theta.R - theta.p + k * t) * shannonLogScale n -
        a t * Real.log (a t) - b t * Real.log (b t)) := by
    filter_upwards [] with t
    simp only [shannonMain, a, b, k]
    ring
  apply (h.congr_of_eventuallyEq heq).congr_deriv
  change
    z.1 - (k * Real.log (a lambda) + a lambda * (k / a lambda)) -
        (-k * Real.log (b lambda) + b lambda * (-k / b lambda)) =
      z.1 - k * (Real.log (a lambda) + 1) +
        k * (Real.log (b lambda) + 1)
  field_simp [ha0, hb0]
  ring

private theorem hasDerivAt_shannonMainFirstFormula (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) {lambda : ℝ}
    (ha : 0 < theta.q + z.1 / shannonLogScale n * lambda)
    (hb : 0 < theta.p - z.1 / shannonLogScale n * lambda) :
    HasDerivAt (shannonMainFirstFormula theta n z)
      (-(z.1 / shannonLogScale n) ^ 2 *
        (1 / (theta.q + z.1 / shannonLogScale n * lambda) +
          1 / (theta.p - z.1 / shannonLogScale n * lambda))) lambda := by
  let k := z.1 / shannonLogScale n
  let a : ℝ → ℝ := fun t ↦ theta.q + k * t
  let b : ℝ → ℝ := fun t ↦ theta.p - k * t
  have ha' : HasDerivAt a k lambda := by
    simpa only [a, id_eq, mul_one] using
      ((hasDerivAt_id lambda).const_mul k).const_add theta.q
  have hb' : HasDerivAt b (-k) lambda := by
    simpa only [b, id_eq, mul_one] using
      ((hasDerivAt_id lambda).const_mul k).const_sub theta.p
  have ha0 : a lambda ≠ 0 := by simpa only [a, k] using ha.ne'
  have hb0 : b lambda ≠ 0 := by simpa only [b, k] using hb.ne'
  have hsub := (hasDerivAt_const lambda z.1).sub
    ((ha'.log ha0).const_mul k)
  have h := hsub.add
    ((hb'.log hb0).const_mul k)
  have heq : shannonMainFirstFormula theta n z =ᶠ[𝓝 lambda]
      (fun t ↦ z.1 - k * Real.log (a t) + k * Real.log (b t)) := by
    filter_upwards [] with t
    simp only [shannonMainFirstFormula, a, b, k]
    ring
  apply (h.congr_of_eventuallyEq heq).congr_deriv
  change 0 - k * (k / a lambda) + k * (-k / b lambda) =
    -(k ^ 2) * (1 / a lambda + 1 / b lambda)
  field_simp [ha0, hb0]
  ring

private theorem shannonMain_iteratedDeriv_one (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) :
    iteratedDeriv (shannonMain theta n z) 1 0 =
      z.1 * (1 + Real.log (theta.p / theta.q) /
        shannonLogScale n) := by
  change deriv (shannonMain theta n z) 0 = _
  rw [(hasDerivAt_shannonMain theta n z
    (lambda := 0)
    (by simpa using theta.q_pos) (by simpa using theta.p_pos)).deriv]
  unfold shannonMainFirstFormula
  simp only [mul_zero, add_zero, sub_zero]
  rw [Real.log_div theta.p_pos.ne' theta.q_pos.ne']
  field_simp [(shannonLogScale_pos n).ne']
  ring

private theorem shannonMain_iteratedDeriv_two (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) :
    iteratedDeriv (shannonMain theta n z) 2 0 =
      -(z.1 / shannonLogScale n) ^ 2 *
        (1 / theta.q + 1 / theta.p) := by
  change deriv (deriv (shannonMain theta n z)) 0 = _
  have hpositive : ∀ᶠ lambda in 𝓝 (0 : ℝ),
      0 < theta.q + z.1 / shannonLogScale n * lambda ∧
      0 < theta.p - z.1 / shannonLogScale n * lambda := by
    have hqa : ContinuousAt
        (fun lambda ↦ theta.q + z.1 / shannonLogScale n * lambda) 0 := by
      fun_prop
    have hpa : ContinuousAt
        (fun lambda ↦ theta.p - z.1 / shannonLogScale n * lambda) 0 := by
      fun_prop
    exact (hqa.eventually_const_lt (by simpa using theta.q_pos)).and
      (hpa.eventually_const_lt (by simpa using theta.p_pos))
  have heq : deriv (shannonMain theta n z) =ᶠ[𝓝 0]
      shannonMainFirstFormula theta n z := by
    filter_upwards [hpositive] with lambda hlambda
    exact (hasDerivAt_shannonMain theta n z hlambda.1 hlambda.2).deriv
  rw [Filter.EventuallyEq.deriv_eq heq]
  simpa only [mul_zero, add_zero, sub_zero] using
    (hasDerivAt_shannonMainFirstFormula theta n z
      (lambda := 0)
      (by simpa using theta.q_pos) (by simpa using theta.p_pos)).deriv

private theorem shannonKOne_one_eq_error_add_main (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) :
    shannonKOne theta n z 1 =
      iteratedDeriv (shannonError theta n z) 1 0 +
        iteratedDeriv (shannonMain theta n z) 1 0 := by
  letI := shannonIndexNonempty theta n
  have hEntropy := hasDerivAt_entropyLine_one
    (shannonLineData theta n z) (linePositiveZero _)
  have hMain := hasDerivAt_shannonMain theta n z
    (lambda := 0)
    (by simpa using theta.q_pos) (by simpa using theta.p_pos)
  unfold shannonKOne entropyLineFirst shannonError
  change deriv (entropyLine (shannonLineData theta n z) 1) 0 =
    deriv (fun lambda ↦ entropyLine (shannonLineData theta n z) 1 lambda -
      shannonMain theta n z lambda) 0 + deriv (shannonMain theta n z) 0
  change deriv (entropyLine (shannonLineData theta n z) 1) 0 =
    deriv (entropyLine (shannonLineData theta n z) 1 -
      shannonMain theta n z) 0 + deriv (shannonMain theta n z) 0
  rw [hEntropy.deriv, (hEntropy.sub hMain).deriv, hMain.deriv]
  ring

private theorem shannonKTwo_one_eq_error_add_main (theta : ShannonData)
    (n : ℕ) (z : ℝ × ℝ) :
    shannonKTwo theta n z 1 =
      iteratedDeriv (shannonError theta n z) 2 0 +
        iteratedDeriv (shannonMain theta n z) 2 0 := by
  letI := shannonIndexNonempty theta n
  let H := entropyLine (shannonLineData theta n z) 1
  let M := shannonMain theta n z
  have hposNhd : ∀ᶠ lambda in 𝓝 (0 : ℝ),
      LinePositive (shannonLineData theta n z) lambda :=
    (isOpen_setOf_linePositive _).mem_nhds (linePositiveZero _)
  have hmainPos : ∀ᶠ lambda in 𝓝 (0 : ℝ),
      0 < theta.q + z.1 / shannonLogScale n * lambda ∧
      0 < theta.p - z.1 / shannonLogScale n * lambda := by
    have hqa : ContinuousAt
        (fun lambda ↦ theta.q + z.1 / shannonLogScale n * lambda) 0 := by
      fun_prop
    have hpa : ContinuousAt
        (fun lambda ↦ theta.p - z.1 / shannonLogScale n * lambda) 0 := by
      fun_prop
    exact (hqa.eventually_const_lt (by simpa using theta.q_pos)).and
      (hpa.eventually_const_lt (by simpa using theta.p_pos))
  have hfirstEq : deriv (fun lambda ↦ H lambda - M lambda) =ᶠ[𝓝 0]
      (fun lambda ↦ deriv H lambda - deriv M lambda) := by
    filter_upwards [hposNhd, hmainPos] with lambda hline hmain
    have hH := hasDerivAt_entropyLine_one (shannonLineData theta n z) hline
    have hM := hasDerivAt_shannonMain theta n z hmain.1 hmain.2
    have hHd : deriv H lambda =
        shannonLineSlope (shannonLineData theta n z) lambda := by
      simpa only [H] using hH.deriv
    have hMd : deriv M lambda =
        shannonMainFirstFormula theta n z lambda := by
      simpa only [M] using hM.deriv
    change deriv (H - M) lambda = deriv H lambda - deriv M lambda
    calc
      deriv (H - M) lambda =
          shannonLineSlope (shannonLineData theta n z) lambda -
            shannonMainFirstFormula theta n z lambda := by
        simpa only [H, M] using (hH.sub hM).deriv
      _ = deriv H lambda - deriv M lambda := by rw [hHd, hMd]
  have hHderivEq : deriv H =ᶠ[𝓝 0]
      entropyLineFirst (shannonLineData theta n z) 1 := by
    filter_upwards [hposNhd] with lambda hline
    calc
      deriv H lambda = shannonLineSlope (shannonLineData theta n z) lambda := by
        simpa only [H] using
          (hasDerivAt_entropyLine_one (shannonLineData theta n z) hline).deriv
      _ = entropyLineFirst (shannonLineData theta n z) 1 lambda :=
        (entropyLineFirst_one (shannonLineData theta n z) hline).symm
  have hHfirst := hasDerivAt_entropyLineFirst_one
    (shannonLineData theta n z) (linePositiveZero _)
  have hMfirst := hasDerivAt_shannonMainFirstFormula theta n z
    (lambda := 0)
    (by simpa using theta.q_pos) (by simpa using theta.p_pos)
  have hMderivEq : deriv M =ᶠ[𝓝 0] shannonMainFirstFormula theta n z := by
    filter_upwards [hmainPos] with lambda hmain
    exact (hasDerivAt_shannonMain theta n z hmain.1 hmain.2).deriv
  unfold shannonKTwo entropyLineSecond secondDeriv shannonError
  change deriv (deriv H) 0 =
    deriv (deriv (fun lambda ↦ H lambda - M lambda)) 0 +
      deriv (deriv M) 0
  rw [Filter.EventuallyEq.deriv_eq hfirstEq]
  change deriv (deriv H) 0 =
    deriv (deriv H - deriv M) 0 + deriv (deriv M) 0
  have hsubDerivEq := hHderivEq.sub hMderivEq
  rw [Filter.EventuallyEq.deriv_eq hHderivEq,
    Filter.EventuallyEq.deriv_eq hsubDerivEq,
    Filter.EventuallyEq.deriv_eq hMderivEq,
    (hHfirst.sub hMfirst).deriv, hHfirst.deriv, hMfirst.deriv]
  ring

/-! ## Compact-uniform consequences -/

private theorem compactUniformError_bounds_of_point_bound
    {U : Type*} (K : Set U) (hK0 : K.Nonempty)
    (fN : ℕ → U → ℝ) (f : U → ℝ) (n : ℕ) (B : ℝ)
    (hB : ∀ x ∈ K, |fN n x - f x| ≤ B) :
    0 ≤ compactUniformError K fN f n ∧
      compactUniformError K fN f n ≤ B := by
  obtain ⟨x0, hx0⟩ := hK0
  unfold compactUniformError
  constructor
  · exact (abs_nonneg _).trans
      (le_csSup ⟨B, fun r hr ↦ by
        rcases hr with ⟨x, hx, rfl⟩
        exact hB x hx⟩ ⟨x0, hx0, rfl⟩)
  · apply csSup_le
    · exact ⟨_, x0, hx0, rfl⟩
    · intro r hr
      rcases hr with ⟨x, hx, rfl⟩
      exact hB x hx

private theorem abs_shannonError_iterated_zero_le_Ctwo
    (theta : ShannonData) (K : Set (ℝ × ℝ))
    (hK : IsCompact K) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hpos : ∀ (n : ℕ) (z : ℝ × ℝ), z ∈ K →
      letI := shannonIndexNonempty theta n
      ∀ lambda ∈ Icc (-epsilon) epsilon,
        LinePositive (shannonLineData theta n z) lambda)
    (j : ℕ) (hj : j ≤ 2) (n : ℕ) (z : ℝ × ℝ) (hz : z ∈ K) :
    |iteratedDeriv (shannonError theta n z) j 0| ≤
      shannonCtwoError theta K (epsilon / 2) j n := by
  have hzero : (0 : ℝ) ∈ Icc (-(epsilon / 2)) (epsilon / 2) := by
    constructor <;> linarith [hepsilon]
  rw [shannonCtwoError_eq_jetUniformError theta K
    epsilon hepsilon hpos j hj n,
    shannonError_jet_eq theta n z epsilon hepsilon
      (hpos n z hz) 0 (by simpa only [neg_div] using hzero) j hj]
  have houter : (0 : ℝ) ∈ Icc (-epsilon) epsilon := by
    constructor <;> linarith [hepsilon]
  have hideal := shannonExpansionIdeal_jet_zero theta n z 0
    (shannonExpansionIdeal_mem_domain theta n z 0
      (hpos n z hz 0 houter)) j hj
  have hrewrite :
      |shannonExpansionJet theta j
          (shannonExpansionActual theta n, z, 0)| =
        |shannonExpansionJet theta j
            (shannonExpansionActual theta n, z, 0) -
          shannonExpansionJet theta j
            (shannonExpansionIdeal n, z, 0)| := by
    rw [hideal, sub_zero]
  rw [hrewrite]
  let Q : Set ((ℝ × ℝ) × ℝ) :=
    K ×ˢ Icc (-(epsilon / 2)) (epsilon / 2)
  let F : ((ℝ × ℝ) × ℝ) → ℝ := fun y ↦
    |shannonExpansionJet theta j
        (shannonExpansionActual theta n, y.1, y.2) -
      shannonExpansionJet theta j
        (shannonExpansionIdeal n, y.1, y.2)|
  have hQ : IsCompact Q := hK.prod isCompact_Icc
  have hactual : ContinuousOn
      (fun y : ((ℝ × ℝ) × ℝ) ↦
        shannonExpansionJet theta j
          (shannonExpansionActual theta n, y.1, y.2)) Q := by
    apply (continuousOn_shannonExpansionJet theta j hj).comp
      (by fun_prop)
    intro y hy
    exact shannonExpansionActual_mem_domain theta n y.1 y.2
      (hpos n y.1 hy.1 y.2 (by
        constructor <;> linarith [hy.2.1, hy.2.2, hepsilon]))
  have hidealContinuous : ContinuousOn
      (fun y : ((ℝ × ℝ) × ℝ) ↦
        shannonExpansionJet theta j
          (shannonExpansionIdeal n, y.1, y.2)) Q := by
    apply (continuousOn_shannonExpansionJet theta j hj).comp
      (by fun_prop)
    intro y hy
    exact shannonExpansionIdeal_mem_domain theta n y.1 y.2
      (hpos n y.1 hy.1 y.2 (by
        constructor <;> linarith [hy.2.1, hy.2.2, hepsilon]))
  have hF : ContinuousOn F Q := (hactual.sub hidealContinuous).abs
  have hset :
      {r : ℝ | ∃ z ∈ K, ∃ lambda ∈ Icc (-(epsilon / 2)) (epsilon / 2),
        r = |shannonExpansionJet theta j
              (shannonExpansionActual theta n, z, lambda) -
            shannonExpansionJet theta j
              (shannonExpansionIdeal n, z, lambda)|} = F '' Q := by
    ext r
    constructor
    · rintro ⟨y, hy, lambda, hlambda, rfl⟩
      exact ⟨(y, lambda), ⟨hy, hlambda⟩, rfl⟩
    · rintro ⟨⟨y, lambda⟩, ⟨hy, hlambda⟩, rfl⟩
      exact ⟨y, hy, lambda, hlambda, rfl⟩
  unfold shannonExpansionJetUniformError
  rw [hset]
  exact le_csSup (hQ.bddAbove_image hF)
    ⟨(z, 0), ⟨hz, hzero⟩, rfl⟩

private theorem exists_compact_pair_abs_bound (K : Set (ℝ × ℝ))
    (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, |z.1| ≤ B ∧ |z.2| ≤ B := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ × ℝ)
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro z hz
  have hzR : dist z (0 : ℝ × ℝ) ≤ R := by
    simpa only [Metric.mem_closedBall] using hR hz
  have hzNorm : ‖z‖ ≤ R := by simpa only [dist_zero_right] using hzR
  have hz1 : |z.1| ≤ R := by
    calc
      |z.1| = ‖z.1‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖z‖ := norm_fst_le z
      _ ≤ R := hzNorm
  have hz2 : |z.2| ≤ R := by
    calc
      |z.2| = ‖z.2‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖z‖ := norm_snd_le z
      _ ≤ R := hzNorm
  exact ⟨hz1.trans (le_max_left _ _), hz2.trans (le_max_left _ _)⟩

/-- Uniform `C²` control of the rounded Shannon expansion, including the
two exact order-one kernel limits. -/
theorem uniformShannonExpansion
    (theta : ShannonData) (K : Set (ℝ × ℝ))
    (hK : IsCompact K) (hK0 : K.Nonempty) :
    ∃ lambda0 : ℝ, 0 < lambda0 ∧
      (∀ (n : ℕ) (z : ℝ × ℝ), z ∈ K →
        letI := shannonIndexNonempty theta n
        ∀ lambda ∈ Icc (-lambda0) lambda0,
          LinePositive (shannonLineData theta n z) lambda) ∧
      (∀ j : ℕ, j ≤ 2 →
        Tendsto (fun n ↦ shannonCtwoError theta K lambda0 j n)
          atTop (𝓝 0)) ∧
      Tendsto (fun n ↦ compactUniformError K
        (fun m z ↦ shannonKOne theta m z 1) (fun z ↦ z.1) n)
        atTop (𝓝 0) ∧
      Tendsto (fun n ↦ compactUniformError K
        (fun m z ↦ shannonKTwo theta m z 1) (fun _ ↦ 0) n)
        atTop (𝓝 0) := by
  obtain ⟨epsilon, hepsilon, hpos⟩ :=
    exists_uniform_shannonLinePositive theta K hK
  let lambda0 := epsilon / 2
  have hlambda0 : 0 < lambda0 := half_pos hepsilon
  have hpos0 : ∀ (n : ℕ) (z : ℝ × ℝ), z ∈ K →
      letI := shannonIndexNonempty theta n
      ∀ lambda ∈ Icc (-lambda0) lambda0,
        LinePositive (shannonLineData theta n z) lambda := by
    intro n z hz lambda hlambda
    exact hpos n z hz lambda (by
      dsimp only [lambda0] at hlambda
      constructor <;> linarith [hlambda.1, hlambda.2])
  have hCtwo : ∀ j : ℕ, j ≤ 2 →
      Tendsto (fun n ↦ shannonCtwoError theta K lambda0 j n)
        atTop (𝓝 0) := by
    intro j hj
    have hjet := tendsto_shannonExpansionJetUniformError theta K hK hK0
      epsilon hepsilon hpos j hj
    simpa only [lambda0, shannonCtwoError_eq_jetUniformError theta K
      epsilon hepsilon hpos j hj] using hjet
  obtain ⟨B, _hB, hcoord⟩ := exists_compact_pair_abs_bound K hK
  let c1 : ℝ := |Real.log (theta.p / theta.q)|
  let mainOneBound : ℕ → ℝ := fun n ↦
    B * c1 * (shannonLogScale n)⁻¹
  have hmainOneBound : Tendsto mainOneBound atTop (𝓝 0) := by
    simpa only [mainOneBound, mul_zero] using
      (tendsto_const_nhds.mul tendsto_const_nhds).mul
        tendsto_inv_shannonLogScale
  let c2 : ℝ := 1 / theta.q + 1 / theta.p
  let mainTwoBound : ℕ → ℝ := fun n ↦
    (B * (shannonLogScale n)⁻¹) ^ 2 * c2
  have hmainTwoBound : Tendsto mainTwoBound atTop (𝓝 0) := by
    have hlinear : Tendsto (fun n ↦ B * (shannonLogScale n)⁻¹)
        atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul
        tendsto_inv_shannonLogScale
    simpa only [mainTwoBound, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_mul] using (hlinear.pow 2).mul tendsto_const_nhds
  have hfirstPoint : ∀ n : ℕ, ∀ z ∈ K,
      |shannonKOne theta n z 1 - z.1| ≤
        shannonCtwoError theta K lambda0 1 n + mainOneBound n := by
    intro n z hz
    rw [shannonKOne_one_eq_error_add_main,
      shannonMain_iteratedDeriv_one]
    have hrewrite :
        iteratedDeriv (shannonError theta n z) 1 0 +
              z.1 * (1 + Real.log (theta.p / theta.q) /
                shannonLogScale n) - z.1 =
          iteratedDeriv (shannonError theta n z) 1 0 +
            z.1 * Real.log (theta.p / theta.q) /
              shannonLogScale n := by
      ring
    rw [hrewrite]
    calc
      |iteratedDeriv (shannonError theta n z) 1 0 +
          z.1 * Real.log (theta.p / theta.q) /
            shannonLogScale n| ≤
        |iteratedDeriv (shannonError theta n z) 1 0| +
          |z.1 * Real.log (theta.p / theta.q) /
            shannonLogScale n| := abs_add_le _ _
      _ ≤ shannonCtwoError theta K lambda0 1 n + mainOneBound n := by
        apply add_le_add
        · dsimp only [lambda0]
          exact abs_shannonError_iterated_zero_le_Ctwo theta K hK
            epsilon hepsilon hpos 1 (by norm_num) n z hz
        · dsimp only [mainOneBound, c1]
          rw [abs_div, abs_mul, abs_of_pos (shannonLogScale_pos n),
            div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hcoord z hz).1 (abs_nonneg _))
            (inv_nonneg.mpr (shannonLogScale_pos n).le)
  have hsecondPoint : ∀ n : ℕ, ∀ z ∈ K,
      |shannonKTwo theta n z 1 - 0| ≤
        shannonCtwoError theta K lambda0 2 n + mainTwoBound n := by
    intro n z hz
    rw [sub_zero, shannonKTwo_one_eq_error_add_main,
      shannonMain_iteratedDeriv_two]
    calc
      |iteratedDeriv (shannonError theta n z) 2 0 +
          -(z.1 / shannonLogScale n) ^ 2 *
            (1 / theta.q + 1 / theta.p)| ≤
        |iteratedDeriv (shannonError theta n z) 2 0| +
          |-(z.1 / shannonLogScale n) ^ 2 *
            (1 / theta.q + 1 / theta.p)| := abs_add_le _ _
      _ = |iteratedDeriv (shannonError theta n z) 2 0| +
          |(z.1 / shannonLogScale n) ^ 2 *
            (1 / theta.q + 1 / theta.p)| := by
            rw [abs_mul, abs_mul, abs_neg]
      _ ≤ shannonCtwoError theta K lambda0 2 n + mainTwoBound n := by
        apply add_le_add
        · dsimp only [lambda0]
          exact abs_shannonError_iterated_zero_le_Ctwo theta K hK
            epsilon hepsilon hpos 2 (by norm_num) n z hz
        · have hc2 : 0 ≤ 1 / theta.q + 1 / theta.p := by
            exact add_nonneg (one_div_nonneg.mpr theta.q_pos.le)
              (one_div_nonneg.mpr theta.p_pos.le)
          have hratio : |z.1 / shannonLogScale n| ≤
              B * (shannonLogScale n)⁻¹ := by
            rw [abs_div, abs_of_pos (shannonLogScale_pos n),
              div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right (hcoord z hz).1
              (inv_nonneg.mpr (shannonLogScale_pos n).le)
          dsimp only [mainTwoBound, c2]
          rw [abs_mul, abs_pow, abs_of_nonneg hc2]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (abs_nonneg _) hratio 2) hc2
  have hfirst : Tendsto (fun n ↦ compactUniformError K
      (fun m z ↦ shannonKOne theta m z 1) (fun z ↦ z.1) n)
      atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact (compactUniformError_bounds_of_point_bound K hK0
        (fun m z ↦ shannonKOne theta m z 1) (fun z ↦ z.1) n
        (shannonCtwoError theta K lambda0 1 n + mainOneBound n)
        (hfirstPoint n)).1
    · intro n
      exact (compactUniformError_bounds_of_point_bound K hK0
        (fun m z ↦ shannonKOne theta m z 1) (fun z ↦ z.1) n
        (shannonCtwoError theta K lambda0 1 n + mainOneBound n)
        (hfirstPoint n)).2
    · simpa only [zero_add] using (hCtwo 1 (by norm_num)).add hmainOneBound
  have hsecond : Tendsto (fun n ↦ compactUniformError K
      (fun m z ↦ shannonKTwo theta m z 1) (fun _ ↦ 0) n)
      atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact (compactUniformError_bounds_of_point_bound K hK0
        (fun m z ↦ shannonKTwo theta m z 1) (fun _ ↦ 0) n
        (shannonCtwoError theta K lambda0 2 n + mainTwoBound n)
        (hsecondPoint n)).1
    · intro n
      exact (compactUniformError_bounds_of_point_bound K hK0
        (fun m z ↦ shannonKTwo theta m z 1) (fun _ ↦ 0) n
        (shannonCtwoError theta K lambda0 2 n + mainTwoBound n)
        (hsecondPoint n)).2
    · simpa only [zero_add] using (hCtwo 2 (by norm_num)).add hmainTwoBound
  exact ⟨lambda0, hlambda0, hpos0, hCtwo, hfirst, hsecond⟩

/-! ## Uniform control of the finite kernels near order one -/

private theorem exists_abs_bound_of_tendsto_zero (f : ℕ → ℝ)
    (hf : Tendsto f atTop (𝓝 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |f n| ≤ C := by
  have hbounded := Metric.isBounded_range_of_tendsto f hf
  obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : ℝ)
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro n
  have hn := hR ⟨n, rfl⟩
  have hnR : |f n| ≤ R := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hn
  exact hnR.trans (le_max_left _ _)

private theorem continuous_shannonKOne_fixed (theta : ShannonData)
    (n : ℕ) (beta : Param) :
    Continuous (fun z : ℝ × ℝ ↦ shannonKOne theta n z beta) := by
  have heq : (fun z : ℝ × ℝ ↦ shannonKOne theta n z beta) =
      fun z ↦ z.1 * shannonKOne theta n shannonBasisOne beta +
        z.2 * shannonKOne theta n shannonBasisTwo beta := by
    funext z
    conv_lhs => rw [shannonBasisDecomposition z]
    rw [shannonKOne_add, shannonKOne_smul, shannonKOne_smul]
  rw [heq]
  fun_prop

private theorem continuous_shannonKTwo_fixed (theta : ShannonData)
    (n : ℕ) (beta : Param) :
    Continuous (fun z : ℝ × ℝ ↦ shannonKTwo theta n z beta) := by
  have heq : (fun z : ℝ × ℝ ↦ shannonKTwo theta n z beta) =
      fun z ↦
        z.1 ^ 2 * shannonKTwo theta n shannonBasisOne beta +
        z.1 * z.2 *
          (shannonKTwo theta n (shannonBasisOne + shannonBasisTwo) beta -
            shannonKTwo theta n shannonBasisOne beta -
            shannonKTwo theta n shannonBasisTwo beta) +
        z.2 ^ 2 * shannonKTwo theta n shannonBasisTwo beta := by
    funext z
    exact shannonKTwo_basis_decomposition theta n z beta
  rw [heq]
  fun_prop

private theorem exists_uniform_shannonMean_order_deriv_bound_near_one
    (theta : ShannonData) (K : Set (ℝ × ℝ))
    (hK : IsCompact K) (hK0 : K.Nonempty)
    (delta : ℝ) (hdelta0 : 0 < delta)
    (hdelta : delta < min (1 / 2 : ℝ) ((theta.c - 1) / 4)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (z : ℝ × ℝ), z ∈ K →
        ∀ alpha ∈ Icc (1 - delta) (1 + delta),
          |deriv (fun s ↦ shannonMean theta n z s) alpha| ≤ C := by
  obtain ⟨B, hB, hcoord⟩ := exists_compact_pair_abs_bound K hK
  obtain ⟨Cesc, hCesc, hesc⟩ :=
    shannonDedicatedEscortNearOne theta K hK hK0 delta hdelta0 hdelta
  let eta : ℝ := (theta.c - 1) / 2
  have heta : 0 < eta := by
    dsimp only [eta]
    linarith [theta.c_gt_one]
  have hdecay : Tendsto (fun n : ℕ ↦ shannonLogScale n *
      Real.rpow (shannonScale n) (-eta)) atTop (𝓝 0) :=
    tendsto_shannonLogScale_mul_rpow_neg eta heta
  obtain ⟨Edec, hEdec, hEdecBound⟩ :=
    exists_abs_bound_of_tendsto_zero _ hdecay
  let Dlog : ℝ := 18 * shannonLogBaseCoeff theta
  let A0 : ℝ := B / theta.q
  let A1 : ℝ := B / theta.p
  let C : ℝ := Dlog * A0 + Dlog * A1 + Cesc * Edec * B
  have hDlog : 0 ≤ Dlog := by
    dsimp only [Dlog]
    exact mul_nonneg (by norm_num) (shannonLogBaseCoeff_nonneg theta)
  have hA0 : 0 ≤ A0 := div_nonneg hB theta.q_pos.le
  have hA1 : 0 ≤ A1 := div_nonneg hB theta.p_pos.le
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg
      (add_nonneg (mul_nonneg hDlog hA0) (mul_nonneg hDlog hA1))
      (mul_nonneg (mul_nonneg hCesc hEdec) hB)
  refine ⟨C, hC, ?_⟩
  intro n z hz alpha hAlpha
  let L := shannonLogScale n
  let r := Real.rpow (shannonScale n) (-eta)
  have hL : 0 < L := shannonLogScale_pos n
  have hr : 0 ≤ r := Real.rpow_nonneg (shannonScale_pos n).le _
  have hlogDecay : L * r ≤ Edec := by
    have h := hEdecBound n
    rw [abs_of_nonneg (mul_nonneg hL.le hr)] at h
    simpa only [L, r] using h
  have hescortDeriv : ∀ j : Fin 3,
      |deriv (fun s ↦ shannonEscort theta n z j s) alpha| ≤
        Dlog * L := by
    intro j
    rw [abs_deriv_shannonEscort_order]
    calc
      shannonEscort theta n z j alpha *
          |shannonLogBase theta n z j -
            shannonEscortLogMean theta n z alpha| ≤
        1 * shannonLogDiameter theta n z := by
          exact mul_le_mul (shannonEscort_le_one theta n z j alpha)
            (abs_shannonLogBase_sub_escortMean_le theta n z j alpha)
            (abs_nonneg _) zero_le_one
      _ ≤ Dlog * L := by
        simpa only [one_mul, Dlog, L] using shannonLogDiameter_le theta n z
  have hterm0 :
      |deriv (fun s ↦ shannonEscort theta n z 0 s) alpha *
          shannonBlockVelocity theta n z 0| ≤ Dlog * A0 := by
    have hvel : |shannonBlockVelocity theta n z 0| ≤ B / (theta.q * L) := by
      rw [shannonBlockVelocity_zero, abs_div, abs_mul,
        abs_of_pos theta.q_pos, abs_of_pos hL]
      exact div_le_div_of_nonneg_right (hcoord z hz).1
        (mul_pos theta.q_pos hL).le
    rw [abs_mul]
    calc
      |deriv (fun s ↦ shannonEscort theta n z 0 s) alpha| *
          |shannonBlockVelocity theta n z 0| ≤
        (Dlog * L) * (B / (theta.q * L)) :=
          mul_le_mul (hescortDeriv 0) hvel (abs_nonneg _)
            (mul_nonneg hDlog hL.le)
      _ = Dlog * A0 := by
        dsimp only [A0]
        field_simp [theta.q_pos.ne', hL.ne']
  have hterm1 :
      |deriv (fun s ↦ shannonEscort theta n z 1 s) alpha *
          shannonBlockVelocity theta n z 1| ≤ Dlog * A1 := by
    have hvel : |shannonBlockVelocity theta n z 1| ≤ B / (theta.p * L) := by
      rw [shannonBlockVelocity_one, abs_div, abs_neg, abs_mul,
        abs_of_pos theta.p_pos, abs_of_pos hL]
      exact div_le_div_of_nonneg_right (hcoord z hz).1
        (mul_pos theta.p_pos hL).le
    rw [abs_mul]
    calc
      |deriv (fun s ↦ shannonEscort theta n z 1 s) alpha| *
          |shannonBlockVelocity theta n z 1| ≤
        (Dlog * L) * (B / (theta.p * L)) :=
          mul_le_mul (hescortDeriv 1) hvel (abs_nonneg _)
            (mul_nonneg hDlog hL.le)
      _ = Dlog * A1 := by
        dsimp only [A1]
        field_simp [theta.p_pos.ne', hL.ne']
  have hterm2 :
      |deriv (fun s ↦ shannonEscort theta n z 2 s) alpha *
          shannonBlockVelocity theta n z 2| ≤ Cesc * Edec * B := by
    have hthird := (hesc n z hz alpha hAlpha).2
    have hexp : -(theta.c - 1) / 2 = -eta := by
      dsimp only [eta]
      ring
    rw [abs_mul]
    calc
      |deriv (fun s ↦ shannonEscort theta n z 2 s) alpha| *
          |shannonBlockVelocity theta n z 2| ≤
        (Cesc * L * r) * B := by
          apply mul_le_mul
          · simpa only [L, r, hexp] using hthird
          · simpa only [shannonBlockVelocity_two] using (hcoord z hz).2
          · exact abs_nonneg _
          · exact mul_nonneg (mul_nonneg hCesc hL.le) hr
      _ = (Cesc * (L * r)) * B := by ring
      _ ≤ (Cesc * Edec) * B := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogDecay hCesc) hB
      _ = Cesc * Edec * B := rfl
  rw [deriv_shannonMean_order, Fin.sum_univ_three]
  calc
    |deriv (fun s ↦ shannonEscort theta n z 0 s) alpha *
          shannonBlockVelocity theta n z 0 +
        deriv (fun s ↦ shannonEscort theta n z 1 s) alpha *
          shannonBlockVelocity theta n z 1 +
        deriv (fun s ↦ shannonEscort theta n z 2 s) alpha *
          shannonBlockVelocity theta n z 2| ≤
      (|deriv (fun s ↦ shannonEscort theta n z 0 s) alpha *
          shannonBlockVelocity theta n z 0| +
        |deriv (fun s ↦ shannonEscort theta n z 1 s) alpha *
          shannonBlockVelocity theta n z 1|) +
        |deriv (fun s ↦ shannonEscort theta n z 2 s) alpha *
          shannonBlockVelocity theta n z 2| := by
            exact (abs_add_le _ _).trans
              (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (Dlog * A0 + Dlog * A1) + Cesc * Edec * B :=
      add_le_add (add_le_add hterm0 hterm1) hterm2
    _ = C := by rfl

private theorem abs_shannonMean_sub_one_le
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (delta C : ℝ) (hdelta0 : 0 < delta)
    (hderiv : ∀ s ∈ Icc (1 - delta) (1 + delta),
      |deriv (fun t ↦ shannonMean theta n z t) s| ≤ C)
    (alpha : ℝ) (hAlpha : alpha ∈ Icc (1 - delta) (1 + delta)) :
    |shannonMean theta n z alpha - shannonMean theta n z 1| ≤
      C * |alpha - 1| := by
  have hOne : (1 : ℝ) ∈ Icc (1 - delta) (1 + delta) := by
    constructor <;> linarith [hdelta0]
  have hmv := (convex_Icc (1 - delta) (1 + delta)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s ↦ shannonMean theta n z s)
    (f' := fun s ↦ deriv (fun t ↦ shannonMean theta n z t) s)
    (x := 1) (y := alpha)
    (fun s _hs ↦
      ((hasDerivAt_shannonMean_order theta n z s).congr_deriv
        (deriv_shannonMean_order theta n z s).symm).hasDerivWithinAt)
    (fun s hs ↦ by simpa only [Real.norm_eq_abs] using hderiv s hs)
    hOne hAlpha
  simpa only [Real.norm_eq_abs] using hmv

private theorem abs_shannonMean_sq_sub_one_sq_le
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (delta U C : ℝ) (hdelta0 : 0 < delta) (hU : 0 ≤ U)
    (hu : ∀ j, |shannonBlockVelocity theta n z j| ≤ U)
    (hderiv : ∀ s ∈ Icc (1 - delta) (1 + delta),
      |deriv (fun t ↦ shannonMean theta n z t) s| ≤ C)
    (alpha : ℝ) (hAlpha : alpha ∈ Icc (1 - delta) (1 + delta)) :
    |shannonMean theta n z alpha ^ 2 - shannonMean theta n z 1 ^ 2| ≤
      (2 * U * C) * |alpha - 1| := by
  have hOne : (1 : ℝ) ∈ Icc (1 - delta) (1 + delta) := by
    constructor <;> linarith [hdelta0]
  have hhas : ∀ s : ℝ, HasDerivAt
      (fun t ↦ shannonMean theta n z t ^ 2)
      (2 * shannonMean theta n z s *
        deriv (fun t ↦ shannonMean theta n z t) s) s := by
    intro s
    rw [deriv_shannonMean_order]
    have h := (hasDerivAt_shannonMean_order theta n z s).pow 2
    exact h.congr_deriv (by ring)
  have hbound : ∀ s ∈ Icc (1 - delta) (1 + delta),
      ‖2 * shannonMean theta n z s *
        deriv (fun t ↦ shannonMean theta n z t) s‖ ≤ 2 * U * C := by
    intro s hs
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left
        (abs_shannonMean_le theta n z s U hu) (by norm_num))
      (hderiv s hs) (abs_nonneg _) (mul_nonneg (by norm_num) hU)
  have hmv := (convex_Icc (1 - delta) (1 + delta)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s ↦ shannonMean theta n z s ^ 2)
    (f' := fun s ↦ 2 * shannonMean theta n z s *
      deriv (fun t ↦ shannonMean theta n z t) s)
    (x := 1) (y := alpha)
    (fun s _hs ↦ (hhas s).hasDerivWithinAt) hbound
    hOne hAlpha
  simpa only [Real.norm_eq_abs] using hmv

private theorem shannonVar_le_four_velocity_sq
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ)
    (alpha U : ℝ) (hU : 0 ≤ U)
    (hu : ∀ j, |shannonBlockVelocity theta n z j| ≤ U) :
    shannonVar theta n z alpha ≤ 4 * U ^ 2 := by
  calc
    shannonVar theta n z alpha ≤
        (4 * U ^ 2) *
          (∑ j ∈ Finset.univ.erase (0 : Fin 3),
            shannonEscort theta n z j alpha) :=
      shannonVar_le_outside theta n z alpha 0 U hU hu
    _ ≤ (4 * U ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left
        (shannonOutsideMass_le_one theta n z 0 alpha)
        (mul_nonneg (by norm_num) (sq_nonneg U))
    _ = 4 * U ^ 2 := mul_one _

private theorem exists_uniform_shannonFiniteKernel_bound_near_one
    (theta : ShannonData) (K : Set (ℝ × ℝ))
    (hK : IsCompact K) (hK0 : K.Nonempty)
    (delta : ℝ) (hdelta0 : 0 < delta)
    (hdelta : delta < min (1 / 2 : ℝ) ((theta.c - 1) / 4)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (z : ℝ × ℝ), z ∈ K →
        ∀ alpha ∈ Icc (1 - delta) (1 + delta),
          |shannonKOne theta n z (finiteParam alpha)| ≤ C ∧
          |shannonKTwo theta n z (finiteParam alpha)| ≤ C := by
  obtain ⟨B, hB, hcoord⟩ := exists_compact_pair_abs_bound K hK
  obtain ⟨U, hU, hvel⟩ := exists_uniform_shannonVelocity_bound theta K hK
  obtain ⟨Cmean, hCmean, hmeanDeriv⟩ :=
    exists_uniform_shannonMean_order_deriv_bound_near_one theta K hK hK0
      delta hdelta0 hdelta
  obtain ⟨_lambda0, _hlambda0, _hpos, _hCtwo, hone, htwo⟩ :=
    uniformShannonExpansion theta K hK hK0
  let eOne : ℕ → ℝ := fun n ↦ compactUniformError K
    (fun m z ↦ shannonKOne theta m z 1) (fun z ↦ z.1) n
  let eTwo : ℕ → ℝ := fun n ↦ compactUniformError K
    (fun m z ↦ shannonKTwo theta m z 1) (fun _ ↦ 0) n
  obtain ⟨Eone, hEone, hEoneBound⟩ :=
    exists_abs_bound_of_tendsto_zero eOne (by simpa only [eOne] using hone)
  obtain ⟨Etwo, _hEtwo, hEtwoBound⟩ :=
    exists_abs_bound_of_tendsto_zero eTwo (by simpa only [eTwo] using htwo)
  let CfiniteOne : ℝ := (3 / 2 : ℝ) * Cmean
  let CfiniteTwo : ℝ :=
    (3 / 2 : ℝ) * (4 * U ^ 2) + (3 / 2 : ℝ) * (2 * U * Cmean)
  let Cone : ℝ := max (Eone + B) CfiniteOne
  let Ctwo : ℝ := max Etwo CfiniteTwo
  let C : ℝ := max Cone Ctwo
  have hCone : 0 ≤ Cone := by
    exact le_trans (add_nonneg hEone hB) (le_max_left _ _)
  have hC : 0 ≤ C := le_trans hCone (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro n z hz alpha hAlpha
  have hAlphaPos : 0 < alpha := by
    have hdeltaHalf : delta < (1 / 2 : ℝ) := (lt_min_iff.mp hdelta).1
    linarith [hAlpha.1]
  have hAlphaBound : |alpha| ≤ (3 / 2 : ℝ) := by
    rw [abs_of_pos hAlphaPos]
    have hdeltaHalf : delta < (1 / 2 : ℝ) := (lt_min_iff.mp hdelta).1
    linarith [hAlpha.2]
  have hAlphaLe : alpha ≤ (3 / 2 : ℝ) :=
    (le_abs_self alpha).trans hAlphaBound
  by_cases hAlphaOne : alpha = 1
  · subst alpha
    rw [finiteParam_one]
    have hpointOne : |shannonKOne theta n z 1 - z.1| ≤ eOne n := by
      exact compactUniformError_point_le K hK
        (fun m z ↦ shannonKOne theta m z 1) (fun z ↦ z.1) n
        (continuous_shannonKOne_fixed theta n 1).continuousOn
        continuous_fst.continuousOn hz
    have hpointTwo : |shannonKTwo theta n z 1 - 0| ≤ eTwo n := by
      exact compactUniformError_point_le K hK
        (fun m z ↦ shannonKTwo theta m z 1) (fun _ ↦ 0) n
        (continuous_shannonKTwo_fixed theta n 1).continuousOn
        continuous_const.continuousOn hz
    have heOne : eOne n ≤ Eone :=
      (le_abs_self (eOne n)).trans (hEoneBound n)
    have heTwo : eTwo n ≤ Etwo :=
      (le_abs_self (eTwo n)).trans (hEtwoBound n)
    constructor
    · calc
        |shannonKOne theta n z 1| ≤
            |shannonKOne theta n z 1 - z.1| + |z.1| := by
              have := abs_add_le
                (shannonKOne theta n z 1 - z.1) z.1
              simpa only [sub_add_cancel] using this
        _ ≤ eOne n + B := add_le_add hpointOne (hcoord z hz).1
        _ ≤ Eone + B := add_le_add heOne le_rfl
        _ ≤ Cone := le_max_left _ _
        _ ≤ C := le_max_left _ _
    · calc
        |shannonKTwo theta n z 1| =
            |shannonKTwo theta n z 1 - 0| := by rw [sub_zero]
        _ ≤ eTwo n := hpointTwo
        _ ≤ Etwo := heTwo
        _ ≤ Ctwo := le_max_left _ _
        _ ≤ C := le_max_right _ _
  · have hmeanDiff := abs_shannonMean_sub_one_le theta n z
        delta Cmean hdelta0 (hmeanDeriv n z hz) alpha hAlpha
    have hmeanSqDiff := abs_shannonMean_sq_sub_one_sq_le theta n z
      delta U Cmean hdelta0 hU (hvel n z hz) (hmeanDeriv n z hz)
      alpha hAlpha
    have hden : 0 < |1 - alpha| := by
      exact abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hAlphaOne))
    have hweightMean :
        |singularWeight (finiteParam alpha)| *
            |shannonMean theta n z alpha - shannonMean theta n z 1| ≤
          CfiniteOne := by
      rw [singularWeight_finite hAlphaPos.le hAlphaOne, abs_div,
        abs_of_pos hAlphaPos]
      calc
        alpha / |1 - alpha| *
            |shannonMean theta n z alpha - shannonMean theta n z 1| ≤
          alpha / |1 - alpha| * (Cmean * |alpha - 1|) :=
            mul_le_mul_of_nonneg_left hmeanDiff
              (div_nonneg hAlphaPos.le (abs_nonneg _))
        _ = alpha * Cmean := by
          rw [abs_sub_comm alpha 1]
          field_simp [hden.ne']
        _ ≤ CfiniteOne := by
          dsimp only [CfiniteOne]
          exact mul_le_mul_of_nonneg_right hAlphaLe hCmean
    have hweightSq :
        |singularWeight (finiteParam alpha)| *
            |shannonMean theta n z 1 ^ 2 -
              shannonMean theta n z alpha ^ 2| ≤
          (3 / 2 : ℝ) * (2 * U * Cmean) := by
      rw [singularWeight_finite hAlphaPos.le hAlphaOne, abs_div,
        abs_of_pos hAlphaPos, abs_sub_comm
          (shannonMean theta n z 1 ^ 2)
          (shannonMean theta n z alpha ^ 2)]
      calc
        alpha / |1 - alpha| *
            |shannonMean theta n z alpha ^ 2 -
              shannonMean theta n z 1 ^ 2| ≤
          alpha / |1 - alpha| *
            ((2 * U * Cmean) * |alpha - 1|) :=
              mul_le_mul_of_nonneg_left hmeanSqDiff
                (div_nonneg hAlphaPos.le (abs_nonneg _))
        _ = alpha * (2 * U * Cmean) := by
          rw [abs_sub_comm alpha 1]
          field_simp [hden.ne']
        _ ≤ (3 / 2 : ℝ) * (2 * U * Cmean) :=
          mul_le_mul_of_nonneg_right hAlphaLe
            (mul_nonneg (mul_nonneg (by norm_num) hU) hCmean)
    have hvar := shannonVar_le_four_velocity_sq theta n z alpha U hU
      (hvel n z hz)
    constructor
    · rw [shannonKOne_finite theta n z hAlphaPos hAlphaOne, abs_mul]
      exact (hweightMean.trans (le_max_right _ _)).trans (le_max_left _ _)
    · rw [shannonKTwo_finite theta n z hAlphaPos hAlphaOne]
      calc
        |-alpha * shannonVar theta n z alpha +
            singularWeight (finiteParam alpha) *
              (shannonMean theta n z 1 ^ 2 -
                shannonMean theta n z alpha ^ 2)| ≤
          |-alpha * shannonVar theta n z alpha| +
            |singularWeight (finiteParam alpha) *
              (shannonMean theta n z 1 ^ 2 -
                shannonMean theta n z alpha ^ 2)| := abs_add_le _ _
        _ ≤ (3 / 2 : ℝ) * (4 * U ^ 2) +
            (3 / 2 : ℝ) * (2 * U * Cmean) := by
          apply add_le_add
          · rw [abs_mul, abs_neg,
              abs_of_nonneg (shannonVar_nonneg theta n z alpha)]
            exact mul_le_mul hAlphaBound hvar
              (shannonVar_nonneg theta n z alpha)
              (by norm_num : (0 : ℝ) ≤ 3 / 2)
          · simpa only [abs_mul] using hweightSq
        _ = CfiniteTwo := rfl
        _ ≤ Ctwo := le_max_right _ _
        _ ≤ C := le_max_right _ _

private theorem shannonFiniteKernelCompact_of_dominant
    (theta : ShannonData) (K : Set (ℝ × ℝ))
    (hK : IsCompact K) (hK0 : K.Nonempty)
    (alpha : ℝ) (hAlpha : 0 < alpha) (hAlphaOne : alpha ≠ 1)
    (k : Fin 3) (eta : ℝ) (heta : 0 < eta)
    (hgap : ∀ a ∈ ({alpha} : Set ℝ), ∀ j : Fin 3, j ≠ k →
      eta ≤ shannonExponent theta k a - shannonExponent theta j a)
    (vBound : ℕ → ℝ)
    (hv : ∀ n, ∀ z ∈ K,
      |shannonBlockVelocity theta n z k| ≤ vBound n)
    (hvlim : Tendsto vBound atTop (𝓝 0)) :
    Tendsto (fun n ↦ compactUniformError K
        (fun m z ↦ shannonKOne theta m z (finiteParam alpha))
        (fun _ ↦ 0) n) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ compactUniformError K
        (fun m z ↦ shannonKTwo theta m z (finiteParam alpha))
        (fun _ ↦ 0) n) atTop (𝓝 0) := by
  obtain ⟨M, hM, hpref⟩ := exists_shannonPrefactor_ratio_bound theta
    ({alpha} : Set ℝ) isCompact_singleton (singleton_nonempty alpha) k
  obtain ⟨U, hU, hu⟩ := exists_uniform_shannonVelocity_bound theta K hK
  obtain ⟨_C_I, C_K, _hCI, _hCK, hest⟩ :=
    shannonDominantEstimates theta ({alpha} : Set ℝ) k eta M U hM hU
      hpref hgap
  let b : ℕ → ℝ := fun n ↦
    C_K * Real.rpow (shannonScale n) (-eta)
  have hblim : Tendsto b atTop (𝓝 0) := by
    have hr : Tendsto (fun n : ℕ ↦ Real.rpow (shannonScale n) (-eta))
        atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop heta).comp (by
        change Tendsto blockScale atTop atTop
        exact tendsto_blockScale_atTop)
    simpa only [b, mul_zero] using tendsto_const_nhds.mul hr
  let eMass : ℕ → ℝ := fun n ↦ compactUniformError K
    (fun m z ↦ shannonLogMassKernel theta m z 1) (fun _ ↦ 0) n
  have heMassLim : Tendsto eMass atTop (𝓝 0) := by
    simpa only [eMass] using (shannonLogMass theta K hK0 hK).1
  have hmeanApprox : ∀ n, ∀ z ∈ K,
      |shannonMean theta n z alpha -
        shannonBlockVelocity theta n z k| ≤ b n := by
    intro n z hz
    have hm := (hest n z (hu n z hz) alpha (by rfl)).2.1
    dsimp only [b]
    linarith [abs_nonneg (shannonSecond theta n z alpha -
      shannonBlockVelocity theta n z k ^ 2),
      shannonVar_nonneg theta n z alpha]
  have hvar : ∀ n, ∀ z ∈ K,
      shannonVar theta n z alpha ≤ b n := by
    intro n z hz
    have hm := (hest n z (hu n z hz) alpha (by rfl)).2.1
    dsimp only [b]
    linarith [abs_nonneg (shannonMean theta n z alpha -
      shannonBlockVelocity theta n z k),
      abs_nonneg (shannonSecond theta n z alpha -
        shannonBlockVelocity theta n z k ^ 2)]
  have hmeanOne : ∀ n, ∀ z ∈ K,
      |shannonMean theta n z 1| ≤ eMass n := by
    intro n z hz
    have hpoint := compactUniformError_point_le K hK
      (fun m z ↦ shannonLogMassKernel theta m z 1) (fun _ ↦ 0) n
      (by simpa only [shannonLogMassKernel_one] using
        (continuous_shannonMean theta n 1).continuousOn)
      continuous_const.continuousOn hz
    simpa only [eMass, shannonLogMassKernel_one, sub_zero] using hpoint
  let mAlpha : ℕ → ℝ := fun n ↦ b n + vBound n
  have hmAlphaLim : Tendsto mAlpha atTop (𝓝 0) := by
    simpa only [mAlpha, zero_add] using hblim.add hvlim
  have hmeanAlpha : ∀ n, ∀ z ∈ K,
      |shannonMean theta n z alpha| ≤ mAlpha n := by
    intro n z hz
    calc
      |shannonMean theta n z alpha| =
          |(shannonMean theta n z alpha -
              shannonBlockVelocity theta n z k) +
            shannonBlockVelocity theta n z k| := by ring_nf
      _ ≤ |shannonMean theta n z alpha -
              shannonBlockVelocity theta n z k| +
            |shannonBlockVelocity theta n z k| := abs_add_le _ _
      _ ≤ b n + vBound n :=
        add_le_add (hmeanApprox n z hz) (hv n z hz)
      _ = mAlpha n := rfl
  let W : ℝ := |singularWeight (finiteParam alpha)|
  let firstBound : ℕ → ℝ := fun n ↦
    W * (mAlpha n + eMass n)
  let secondBound : ℕ → ℝ := fun n ↦
    alpha * b n + W * (eMass n ^ 2 + mAlpha n ^ 2)
  have hfirstBoundLim : Tendsto firstBound atTop (𝓝 0) := by
    have hsum := hmAlphaLim.add heMassLim
    have hW : Tendsto (fun _ : ℕ ↦ W) atTop (𝓝 W) :=
      tendsto_const_nhds
    simpa only [firstBound, zero_add, mul_zero] using hW.mul hsum
  have hsecondBoundLim : Tendsto secondBound atTop (𝓝 0) := by
    have hleft : Tendsto (fun n ↦ alpha * b n) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hblim
    have hsq : Tendsto (fun n ↦ eMass n ^ 2 + mAlpha n ^ 2)
        atTop (𝓝 0) := by
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] using
        (heMassLim.pow 2).add (hmAlphaLim.pow 2)
    have hright : Tendsto
        (fun n ↦ W * (eMass n ^ 2 + mAlpha n ^ 2)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hsq
    simpa only [secondBound, zero_add] using hleft.add hright
  have hfirstPoint : ∀ n, ∀ z ∈ K,
      |shannonKOne theta n z (finiteParam alpha) - 0| ≤ firstBound n := by
    intro n z hz
    rw [sub_zero, shannonKOne_finite theta n z hAlpha hAlphaOne, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc
      |shannonMean theta n z alpha - shannonMean theta n z 1| ≤
          |shannonMean theta n z alpha| +
            |shannonMean theta n z 1| := abs_sub _ _
      _ ≤ mAlpha n + eMass n :=
        add_le_add (hmeanAlpha n z hz) (hmeanOne n z hz)
      _ = _ := rfl
  have hsecondPoint : ∀ n, ∀ z ∈ K,
      |shannonKTwo theta n z (finiteParam alpha) - 0| ≤ secondBound n := by
    intro n z hz
    rw [sub_zero, shannonKTwo_finite theta n z hAlpha hAlphaOne]
    calc
      |-alpha * shannonVar theta n z alpha +
          singularWeight (finiteParam alpha) *
            (shannonMean theta n z 1 ^ 2 -
              shannonMean theta n z alpha ^ 2)| ≤
        |-alpha * shannonVar theta n z alpha| +
          |singularWeight (finiteParam alpha) *
            (shannonMean theta n z 1 ^ 2 -
              shannonMean theta n z alpha ^ 2)| := abs_add_le _ _
      _ ≤ alpha * b n + W * (eMass n ^ 2 + mAlpha n ^ 2) := by
        apply add_le_add
        · rw [abs_mul, abs_neg, abs_of_pos hAlpha,
            abs_of_nonneg (shannonVar_nonneg theta n z alpha)]
          exact mul_le_mul_of_nonneg_left (hvar n z hz) hAlpha.le
        · rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          calc
            |shannonMean theta n z 1 ^ 2 -
                shannonMean theta n z alpha ^ 2| ≤
              |shannonMean theta n z 1 ^ 2| +
                |shannonMean theta n z alpha ^ 2| := abs_sub _ _
            _ = |shannonMean theta n z 1| ^ 2 +
                |shannonMean theta n z alpha| ^ 2 := by
                  rw [abs_pow, abs_pow]
            _ ≤ eMass n ^ 2 + mAlpha n ^ 2 :=
              add_le_add
                (pow_le_pow_left₀ (abs_nonneg _) (hmeanOne n z hz) 2)
                (pow_le_pow_left₀ (abs_nonneg _) (hmeanAlpha n z hz) 2)
      _ = secondBound n := rfl
  constructor
  · apply squeeze_zero
    · exact fun n ↦ (compactUniformError_bounds_of_point_bound K hK0
        (fun m z ↦ shannonKOne theta m z (finiteParam alpha))
        (fun _ ↦ 0) n (firstBound n) (hfirstPoint n)).1
    · exact fun n ↦ (compactUniformError_bounds_of_point_bound K hK0
        (fun m z ↦ shannonKOne theta m z (finiteParam alpha))
        (fun _ ↦ 0) n (firstBound n) (hfirstPoint n)).2
    · exact hfirstBoundLim
  · apply squeeze_zero
    · exact fun n ↦ (compactUniformError_bounds_of_point_bound K hK0
        (fun m z ↦ shannonKTwo theta m z (finiteParam alpha))
        (fun _ ↦ 0) n (secondBound n) (hsecondPoint n)).1
    · exact fun n ↦ (compactUniformError_bounds_of_point_bound K hK0
        (fun m z ↦ shannonKTwo theta m z (finiteParam alpha))
        (fun _ ↦ 0) n (secondBound n) (hsecondPoint n)).2
    · exact hsecondBoundLim

private theorem shannonFiniteKernelCompact_near_one
    (theta : ShannonData) (K : Set (ℝ × ℝ))
    (hK : IsCompact K) (hK0 : K.Nonempty)
    (delta : ℝ)
    (hdelta : delta < min (1 / 2 : ℝ) ((theta.c - 1) / 4))
    (alpha : ℝ) (hAlpha : alpha ∈ Icc (1 - delta) (1 + delta))
    (hAlphaOne : alpha ≠ 1) :
    Tendsto (fun n ↦ compactUniformError K
        (fun m z ↦ shannonKOne theta m z (finiteParam alpha))
        (fun _ ↦ 0) n) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ compactUniformError K
        (fun m z ↦ shannonKTwo theta m z (finiteParam alpha))
        (fun _ ↦ 0) n) atTop (𝓝 0) := by
  obtain ⟨B, _hB, hcoord⟩ := exists_compact_pair_abs_bound K hK
  have hdeltaHalf : delta < (1 / 2 : ℝ) := (lt_min_iff.mp hdelta).1
  have hdeltaC : delta < (theta.c - 1) / 4 := (lt_min_iff.mp hdelta).2
  have hAlphaPos : 0 < alpha := by linarith [hAlpha.1, hdeltaHalf]
  have hAlphaC : alpha < theta.c := by
    have hc : 1 < theta.c := theta.c_gt_one
    linarith [hAlpha.2, hdeltaC, hc]
  rcases lt_or_gt_of_ne hAlphaOne with hbelow | habove
  · let eta : ℝ := 1 - alpha
    have heta : 0 < eta := sub_pos.mpr hbelow
    have hgap : ∀ a ∈ ({alpha} : Set ℝ), ∀ j : Fin 3, j ≠ 0 →
        eta ≤ shannonExponent theta 0 a - shannonExponent theta j a := by
      intro a ha j hj
      simp only [mem_singleton_iff] at ha
      subst a
      rcases j with ⟨j, hjlt⟩
      interval_cases j
      · exact (hj rfl).elim
      · simp [shannonExponent, shannonCountExponent, shannonAmplitude]
        dsimp only [eta]
        linarith
      · simp [shannonExponent, shannonCountExponent, shannonAmplitude]
        dsimp only [eta]
        linarith [theta.c_gt_one]
    let vBound : ℕ → ℝ := fun n ↦
      (B / theta.q) * (shannonLogScale n)⁻¹
    have hv : ∀ n, ∀ z ∈ K,
        |shannonBlockVelocity theta n z (0 : Fin 3)| ≤ vBound n := by
      intro n z hz
      rw [shannonBlockVelocity_zero, abs_div, abs_mul,
        abs_of_pos theta.q_pos, abs_of_pos (shannonLogScale_pos n)]
      dsimp only [vBound]
      calc
        |z.1| / (theta.q * shannonLogScale n) =
            (|z.1| / theta.q) * (shannonLogScale n)⁻¹ := by
              field_simp [theta.q_pos.ne', (shannonLogScale_pos n).ne']
        _ ≤ (B / theta.q) * (shannonLogScale n)⁻¹ :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (hcoord z hz).1 theta.q_pos.le)
            (inv_nonneg.mpr (shannonLogScale_pos n).le)
    have hvlim : Tendsto vBound atTop (𝓝 0) := by
      simpa only [vBound, mul_zero] using tendsto_const_nhds.mul
        tendsto_inv_shannonLogScale
    exact shannonFiniteKernelCompact_of_dominant theta K hK hK0 alpha
      hAlphaPos hAlphaOne 0 eta heta hgap vBound hv hvlim
  · let eta : ℝ := min (alpha - 1) (theta.c - alpha)
    have heta : 0 < eta :=
      lt_min (sub_pos.mpr habove) (sub_pos.mpr hAlphaC)
    have hgap : ∀ a ∈ ({alpha} : Set ℝ), ∀ j : Fin 3, j ≠ 1 →
        eta ≤ shannonExponent theta 1 a - shannonExponent theta j a := by
      intro a ha j hj
      simp only [mem_singleton_iff] at ha
      subst a
      rcases j with ⟨j, hjlt⟩
      interval_cases j
      · simp [shannonExponent, shannonCountExponent, shannonAmplitude]
        dsimp only [eta]
        linarith [min_le_left (alpha - 1) (theta.c - alpha)]
      · exact (hj rfl).elim
      · simp [shannonExponent, shannonCountExponent, shannonAmplitude]
        dsimp only [eta]
        linarith [min_le_right (alpha - 1) (theta.c - alpha)]
    let vBound : ℕ → ℝ := fun n ↦
      (B / theta.p) * (shannonLogScale n)⁻¹
    have hv : ∀ n, ∀ z ∈ K,
        |shannonBlockVelocity theta n z (1 : Fin 3)| ≤ vBound n := by
      intro n z hz
      rw [shannonBlockVelocity_one, abs_div, abs_neg, abs_mul,
        abs_of_pos theta.p_pos, abs_of_pos (shannonLogScale_pos n)]
      dsimp only [vBound]
      calc
        |z.1| / (theta.p * shannonLogScale n) =
            (|z.1| / theta.p) * (shannonLogScale n)⁻¹ := by
              field_simp [theta.p_pos.ne', (shannonLogScale_pos n).ne']
        _ ≤ (B / theta.p) * (shannonLogScale n)⁻¹ :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (hcoord z hz).1 theta.p_pos.le)
            (inv_nonneg.mpr (shannonLogScale_pos n).le)
    have hvlim : Tendsto vBound atTop (𝓝 0) := by
      simpa only [vBound, mul_zero] using tendsto_const_nhds.mul
        tendsto_inv_shannonLogScale
    exact shannonFiniteKernelCompact_of_dominant theta K hK hK0 alpha
      hAlphaPos hAlphaOne 1 eta heta hgap vBound hv hvlim

/-- Uniform boundedness of both finite-order Shannon kernels on a punctured
neighbourhood of order one, their fixed-order compact-uniform limits, and the
two removable order-one limits. -/
theorem shannonNeighbourhood
    (theta : ShannonData) (K : Set (ℝ × ℝ)) (delta : ℝ)
    (hK : IsCompact K) (hK0 : K.Nonempty)
    (hdelta0 : 0 < delta)
    (hdelta : delta < min (1 / 2 : ℝ) ((theta.c - 1) / 4)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (n : ℕ) (z : ℝ × ℝ), z ∈ K →
        ∀ alpha ∈ Icc (1 - delta) (1 + delta),
          |shannonKOne theta n z (finiteParam alpha)| ≤ C ∧
          |shannonKTwo theta n z (finiteParam alpha)| ≤ C) ∧
      (∀ alpha : ℝ, alpha ∈ Icc (1 - delta) (1 + delta) →
        alpha ≠ 1 →
        Tendsto (fun n ↦ compactUniformError K
          (fun m z ↦ shannonKOne theta m z (finiteParam alpha))
          (fun _ ↦ 0) n) atTop (𝓝 0) ∧
        Tendsto (fun n ↦ compactUniformError K
          (fun m z ↦ shannonKTwo theta m z (finiteParam alpha))
          (fun _ ↦ 0) n) atTop (𝓝 0)) ∧
      Tendsto (fun n ↦ compactUniformError K
        (fun m z ↦ shannonKOne theta m z 1) (fun z ↦ z.1) n)
        atTop (𝓝 0) ∧
      Tendsto (fun n ↦ compactUniformError K
        (fun m z ↦ shannonKTwo theta m z 1) (fun _ ↦ 0) n)
        atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_shannonFiniteKernel_bound_near_one theta K hK hK0
      delta hdelta0 hdelta
  obtain ⟨_lambda0, _hlambda0, _hpos, _hCtwo, hone, htwo⟩ :=
    uniformShannonExpansion theta K hK hK0
  refine ⟨C, hC, hbound, ?_, hone, htwo⟩
  intro alpha hAlpha hAlphaOne
  exact shannonFiniteKernelCompact_near_one theta K hK hK0 delta
    hdelta alpha hAlpha hAlphaOne

end ConditionalEntropy
