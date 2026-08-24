import ConditionalEntropy.ShannonKernelBridges

/-!
# The Shannon curve--kernel bridge

The totalized cone curves agree on a positive neighbourhood with the smooth
signed-integral lines.  This identifies their first two iterated derivatives
without differentiating a value-only equality at an isolated point.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology ContDiff

namespace ConditionalEntropy

private theorem contDiffOn_two_of_derivative_chain
    {U : Set ℝ} (hU : IsOpen U) {f f1 f2 : ℝ → ℝ}
    (h0 : ∀ x ∈ U, HasDerivAt f (f1 x) x)
    (h1 : ∀ x ∈ U, HasDerivAt f1 (f2 x) x)
    (h2 : ContinuousOn f2 U) : ContDiffOn ℝ 2 f U := by
  have hf1 : ContDiffOn ℝ 1 f1 U := by
    rw [contDiffOn_one_iff_derivWithin hU.uniqueDiffOn]
    refine ⟨fun x hx ↦ (h1 x hx).differentiableAt.differentiableWithinAt, ?_⟩
    exact h2.congr fun x hx ↦ by
      rw [derivWithin_of_isOpen hU hx]
      exact (h1 x hx).deriv
  rw [show (2 : ℕ∞ω) = 1 + 1 by rfl,
    contDiffOn_succ_iff_deriv_of_isOpen hU]
  refine ⟨fun x hx ↦ (h0 x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro h
    simp at h
  · exact hf1.congr fun x hx ↦ (h0 x hx).deriv

private theorem iteratedDeriv_eq_of_eqOn_open_two
    {f g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U)
    (hfg : Set.EqOn f g U) (q : ℕ) (hq : q ≤ 2) :
    iteratedDeriv f q x = iteratedDeriv g q x := by
  interval_cases q
  · simp only [iteratedDeriv_zero]
    exact hfg hx
  · change deriv f x = deriv g x
    exact (Filter.EventuallyEq.deriv_eq
      (eventuallyEq_of_mem (hU.mem_nhds hx) hfg))
  · change deriv (deriv f) x = deriv (deriv g) x
    have hderiv : deriv f =ᶠ[nhds x] deriv g := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact Filter.EventuallyEq.deriv_eq
        (eventuallyEq_of_mem (hU.mem_nhds hy) hfg)
    exact Filter.EventuallyEq.deriv_eq hderiv

/-- Exact Shannon curve--kernel bridge through derivative order two. -/
theorem shannonCurveKernelBridge (mu : SignedMeasure Param)
    (theta : ShannonData) (n : ℕ) (z : ℝ × ℝ) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      (∀ lambda ∈ Ioo (-epsilon) epsilon,
        LinePositive (shannonLineData theta n z) lambda) ∧
      0 < shannonPhiCurve mu theta n z 0 ∧
      ContDiffOn ℝ 2 (fun lambda ↦ shannonPhiCurve mu theta n z lambda)
        (Ioo (-epsilon) epsilon) ∧
      ContDiffOn ℝ 2 (shannonGCurve mu theta n z)
        (Ioo (-epsilon) epsilon) ∧
      (∀ q : ℕ, q ≤ 2 →
        iteratedDeriv
          (fun lambda ↦ Real.log (shannonPhiCurve mu theta n z lambda)) q 0 =
            shannonLogKernel mu theta n z q) ∧
      (∀ q : ℕ, q ≤ 2 →
        iteratedDeriv (shannonGCurve mu theta n z) q 0 =
          shannonGKernel mu theta n z q) := by
  letI := shannonIndexNonempty theta n
  let L := shannonLineData theta n z
  obtain ⟨epsilon, hepsilon, hpos, hIntegral, hcont0, hcont1, hcont2⟩ :=
    shannonIntegralDerivativePackage mu theta n z
  let U : Set ℝ := Ioo (-epsilon) epsilon
  let f0 : ℝ → ℝ := fun lambda ↦
    signedIntegral mu (fun beta ↦ entropyLine L beta lambda)
  let f1 : ℝ → ℝ := fun lambda ↦
    signedIntegral mu (fun beta ↦ entropyLineFirst L beta lambda)
  let f2 : ℝ → ℝ := fun lambda ↦
    signedIntegral mu (fun beta ↦ entropyLineSecond L beta lambda)
  have hzero : (0 : ℝ) ∈ U := by
    dsimp only [U]
    constructor <;> linarith
  have hderiv0 : ∀ lambda ∈ U, HasDerivAt f0 (f1 lambda) lambda := by
    intro lambda hlambda
    have h := (hIntegral lambda hlambda).1
    change HasDerivAt
      (fun x ↦ signedIntegral mu (fun beta ↦
        entropyLine (shannonLineData theta n z) beta x))
      (signedIntegral mu (fun beta ↦
        entropyLineFirst (shannonLineData theta n z) beta lambda)) lambda at h
    simpa only [f0, f1, L] using h
  have hderiv1 : ∀ lambda ∈ U, HasDerivAt f1 (f2 lambda) lambda := by
    intro lambda hlambda
    simpa only [f1, f2, L] using (hIntegral lambda hlambda).2
  have hf2cont : ContinuousOn f2 U := by
    simpa only [f2, L, U] using hcont2
  have hf0cd : ContDiffOn ℝ 2 f0 U :=
    contDiffOn_two_of_derivative_chain isOpen_Ioo hderiv0 hderiv1 hf2cont
  have hGEq : Set.EqOn (shannonGCurve mu theta n z) f0 U := by
    intro lambda hlambda
    simpa only [f0, L, integratedEntropyLine] using
      shannonGCurve_of_positive mu theta n z (hpos lambda hlambda)
  have hGcd : ContDiffOn ℝ 2 (shannonGCurve mu theta n z) U :=
    hf0cd.congr fun lambda hlambda ↦ hGEq hlambda
  have hmassCd : ContDiffOn ℝ 2 (lineMass L) U := by
    unfold lineMass lineRaw
    fun_prop
  have hlogMassCd : ContDiffOn ℝ 2
      (fun lambda ↦ Real.log (lineMass L lambda)) U :=
    hmassCd.log fun lambda hlambda ↦
      (lineMass_pos L (hpos lambda hlambda)).ne'
  have hsignedLogCd : ContDiffOn ℝ 2 (signedLogPhiLine mu L) U := by
    change ContDiffOn ℝ 2
      ((fun lambda ↦ Real.log (lineMass L lambda)) + f0) U
    exact hlogMassCd.add hf0cd
  have hexpCd : ContDiffOn ℝ 2
      (fun lambda ↦ Real.exp (signedLogPhiLine mu L lambda)) U :=
    hsignedLogCd.exp
  have hPhiEq : Set.EqOn (fun lambda ↦ shannonPhiCurve mu theta n z lambda)
      (fun lambda ↦ Real.exp (signedLogPhiLine mu L lambda)) U := by
    intro lambda hlambda
    have hphi := shannonPhiCurve_pos_of_positive mu theta n z (hpos lambda hlambda)
    calc
      shannonPhiCurve mu theta n z lambda =
          Real.exp (Real.log (shannonPhiCurve mu theta n z lambda)) :=
        (Real.exp_log hphi).symm
      _ = Real.exp (signedLogPhiLine mu L lambda) := by
        rw [log_shannonPhiCurve_of_positive mu theta n z (hpos lambda hlambda)]
  have hPhiCd : ContDiffOn ℝ 2
      (fun lambda ↦ shannonPhiCurve mu theta n z lambda) U :=
    hexpCd.congr fun lambda hlambda ↦ hPhiEq hlambda
  have hLogEq : Set.EqOn
      (fun lambda ↦ Real.log (shannonPhiCurve mu theta n z lambda))
      (signedLogPhiLine mu L) U := by
    intro lambda hlambda
    exact log_shannonPhiCurve_of_positive mu theta n z (hpos lambda hlambda)
  refine ⟨epsilon, hepsilon, hpos,
    shannonPhiCurve_zero_pos mu theta n z, ?_, ?_, ?_, ?_⟩
  · simpa only [U] using hPhiCd
  · simpa only [U] using hGcd
  · intro q hq
    have hqeq := iteratedDeriv_eq_of_eqOn_open_two isOpen_Ioo hzero hLogEq q hq
    simpa only [shannonLogKernel, L] using hqeq
  · intro q hq
    have hqeq := iteratedDeriv_eq_of_eqOn_open_two isOpen_Ioo hzero hGEq q hq
    unfold shannonGKernel
    change iteratedDeriv (shannonGCurve mu theta n z) q 0 =
      iteratedDeriv
        (fun lambda ↦ signedIntegral mu (fun beta ↦
          entropyLine (shannonLineData theta n z) beta lambda)) q 0
    simpa only [f0, L] using hqeq

end ConditionalEntropy
