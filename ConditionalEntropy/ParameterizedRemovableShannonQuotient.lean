import ConditionalEntropy.EndpointLineCalculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# A parameterized removable quotient at the Shannon point

This file proves the local, finite-regularity version of the removable-quotient
lemma used in the manuscript.  In particular, commutation of the relevant
mixed partials is derived from `C^3` regularity.
-/

noncomputable section

open Filter Set MeasureTheory intervalIntegral
open scoped Topology Interval

namespace ConditionalEntropy

private def alphaDirection : ℝ × ℝ := (1, 0)

private def lambdaDirection : ℝ × ℝ := (0, 1)

private def partialAlpha (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ F p alphaDirection

private def partialLambda (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ F p lambdaDirection

private theorem deriv_fst_slice_eq_partialAlpha
    (G : ℝ × ℝ → ℝ) {p : ℝ × ℝ}
    (hG : DifferentiableAt ℝ G p) :
    deriv (fun a : ℝ => G (a, p.2)) p.1 = partialAlpha G p := by
  have h := (hG.hasFDerivAt.comp p.1
    (hasFDerivAt_prodMk_left p.1 p.2)).hasDerivAt
  change deriv (G ∘ fun a : ℝ => (a, p.2)) p.1 = partialAlpha G p
  simpa [partialAlpha, alphaDirection] using h.deriv

private theorem deriv_snd_slice_eq_partialLambda
    (G : ℝ × ℝ → ℝ) {p : ℝ × ℝ}
    (hG : DifferentiableAt ℝ G p) :
    deriv (fun lambda : ℝ => G (p.1, lambda)) p.2 = partialLambda G p := by
  have h := (hG.hasFDerivAt.comp p.2
    (hasFDerivAt_prodMk_right p.1 p.2)).hasDerivAt
  change deriv (G ∘ fun lambda : ℝ => (p.1, lambda)) p.2 = partialLambda G p
  simpa [partialLambda, lambdaDirection] using h.deriv

private theorem contDiffOn_partialAlpha_two
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) : ContDiffOn ℝ 2 (partialAlpha G) D := by
  exact (hG.fderiv_of_isOpen hD (m := 2) (by norm_num)).clm_apply contDiffOn_const

private theorem contDiffOn_partialLambda_two
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) : ContDiffOn ℝ 2 (partialLambda G) D := by
  exact (hG.fderiv_of_isOpen hD (m := 2) (by norm_num)).clm_apply contDiffOn_const

private theorem contDiffOn_partialLambda_one
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 2 G D) : ContDiffOn ℝ 1 (partialLambda G) D := by
  exact (hG.fderiv_of_isOpen hD (m := 1) (by norm_num)).clm_apply contDiffOn_const

private theorem hasDerivAt_partialAlpha_snd
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 2 G D) {p : ℝ × ℝ} (hp : p ∈ D) :
    HasDerivAt (fun lambda : ℝ => partialAlpha G (p.1, lambda))
      (partialAlpha (partialLambda G) p) p.2 := by
  have hGp : ContDiffAt ℝ 2 G p := (hG p hp).contDiffAt (hD.mem_nhds hp)
  have hDGp : DifferentiableAt ℝ (fderiv ℝ G) p :=
    (hGp.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hAp : DifferentiableAt ℝ (partialAlpha G) p :=
    hDGp.clm_apply (differentiableAt_const alphaDirection)
  have hs : HasDerivAt (fun lambda : ℝ => partialAlpha G (p.1, lambda))
      (fderiv ℝ (partialAlpha G) p lambdaDirection) p.2 := by
    have hs' := (hAp.hasFDerivAt.comp p.2
      (hasFDerivAt_prodMk_right p.1 p.2)).hasDerivAt
    simpa [Function.comp_def, lambdaDirection] using hs'
  have hsymm := hGp.isSymmSndFDerivAt (by norm_num)
  have heq : fderiv ℝ (partialAlpha G) p lambdaDirection =
      partialAlpha (partialLambda G) p := by
    rw [show partialAlpha G = fun q => fderiv ℝ G q alphaDirection from rfl,
      fderiv_clm_apply hDGp (differentiableAt_const alphaDirection)]
    rw [show partialLambda G = fun q => fderiv ℝ G q lambdaDirection from rfl,
      show partialAlpha (fun q => fderiv ℝ G q lambdaDirection) p =
        fderiv ℝ (fun q => fderiv ℝ G q lambdaDirection) p alphaDirection from rfl,
      fderiv_clm_apply hDGp (differentiableAt_const lambdaDirection)]
    simp only [alphaDirection, lambdaDirection,
      ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearMap.flip_apply, fderiv_const_apply, zero_apply,
      map_zero, zero_add]
    exact hsymm lambdaDirection alphaDirection
  exact hs.congr_deriv heq

private theorem lambdaDeriv_one_eq_partialLambda
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G D) {p : ℝ × ℝ} (hp : p ∈ D) :
    lambdaDeriv G 1 p.1 p.2 = partialLambda G p := by
  have hGp : DifferentiableAt ℝ G p :=
    ((hG p hp).contDiffAt (hD.mem_nhds hp)).differentiableAt one_ne_zero
  exact deriv_snd_slice_eq_partialLambda G hGp

private theorem lambdaDeriv_two_eq_partialLambda_two
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 2 G D) {p : ℝ × ℝ} (hp : p ∈ D) :
    lambdaDeriv G 2 p.1 p.2 = partialLambda (partialLambda G) p := by
  have hL : ContDiffOn ℝ 1 (partialLambda G) D :=
    contDiffOn_partialLambda_one hD hG
  have hLp : DifferentiableAt ℝ (partialLambda G) p :=
    ((hL p hp).contDiffAt (hD.mem_nhds hp)).differentiableAt one_ne_zero
  have hmem : Filter.Eventually (fun lambda : ℝ => (p.1, lambda) ∈ D) (nhds p.2) := by
    exact (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds (hD.mem_nhds hp)
  have heq : Filter.EventuallyEq (nhds p.2)
      (fun lambda : ℝ => lambdaDeriv G 1 p.1 lambda)
      (fun lambda : ℝ => partialLambda G (p.1, lambda)) := by
    filter_upwards [hmem] with lambda hlambda
    exact lambdaDeriv_one_eq_partialLambda hD (hG.of_le (by norm_num)) hlambda
  change deriv (fun lambda : ℝ => lambdaDeriv G 1 p.1 lambda) p.2 = _
  rw [heq.deriv_eq]
  exact deriv_snd_slice_eq_partialLambda (partialLambda G) hLp

private theorem contDiffOn_lambdaDeriv_one_two
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => lambdaDeriv G 1 p.1 p.2) D := by
  exact (contDiffOn_partialLambda_two hD hG).congr fun p hp =>
    lambdaDeriv_one_eq_partialLambda hD (hG.of_le (by norm_num)) hp

private theorem contDiffOn_lambdaDeriv_two_one
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => lambdaDeriv G 2 p.1 p.2) D := by
  have hL : ContDiffOn ℝ 2 (partialLambda G) D :=
    contDiffOn_partialLambda_two hD hG
  have hLL : ContDiffOn ℝ 1 (partialLambda (partialLambda G)) D :=
    contDiffOn_partialLambda_one hD hL
  exact hLL.congr fun p hp =>
    lambdaDeriv_two_eq_partialLambda_two hD (hG.of_le (by norm_num)) hp

private theorem contDiffOn_lambdaDeriv_of_le_two
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) {j : ℕ} (hj : j ≤ 2) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => lambdaDeriv G j p.1 p.2) D := by
  interval_cases j
  · simpa [lambdaDeriv] using hG.of_le (by norm_num)
  · exact (contDiffOn_lambdaDeriv_one_two hD hG).of_le (by norm_num)
  · exact contDiffOn_lambdaDeriv_two_one hD hG

private theorem alphaLambdaDeriv_eq_partialAlpha
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) {j : ℕ} (hj : j ≤ 2)
    {p : ℝ × ℝ} (hp : p ∈ D) :
    alphaLambdaDeriv G j p.1 p.2 =
      partialAlpha (fun q : ℝ × ℝ => lambdaDeriv G j q.1 q.2) p := by
  let Gj : ℝ × ℝ → ℝ := fun q => lambdaDeriv G j q.1 q.2
  have hGj := contDiffOn_lambdaDeriv_of_le_two hD hG hj
  have hGjp : DifferentiableAt ℝ Gj p :=
    ((hGj p hp).contDiffAt (hD.mem_nhds hp)).differentiableAt one_ne_zero
  exact deriv_fst_slice_eq_partialAlpha Gj hGjp

private theorem contDiffOn_alphaLambdaDeriv
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) {j : ℕ} (hj : j ≤ 2) :
    ContDiffOn ℝ 0 (fun p : ℝ × ℝ => alphaLambdaDeriv G j p.1 p.2) D := by
  let Gj : ℝ × ℝ → ℝ := fun q => lambdaDeriv G j q.1 q.2
  have hGj := contDiffOn_lambdaDeriv_of_le_two hD hG hj
  have hA : ContDiffOn ℝ 0 (partialAlpha Gj) D :=
    ((hGj.fderiv_of_isOpen hD (m := 0) (by norm_num)).clm_apply contDiffOn_const)
  exact hA.congr fun p hp => alphaLambdaDeriv_eq_partialAlpha hD hG hj hp

private theorem hasDerivAt_lambdaDeriv_fst
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) {j : ℕ} (hj : j ≤ 2)
    {p : ℝ × ℝ} (hp : p ∈ D) :
    HasDerivAt (fun a : ℝ => lambdaDeriv G j a p.2)
      (alphaLambdaDeriv G j p.1 p.2) p.1 := by
  let Gj : ℝ × ℝ → ℝ := fun q => lambdaDeriv G j q.1 q.2
  have hGj := contDiffOn_lambdaDeriv_of_le_two hD hG hj
  have hGjp : DifferentiableAt ℝ Gj p :=
    ((hGj p hp).contDiffAt (hD.mem_nhds hp)).differentiableAt one_ne_zero
  have hs := (hGjp.hasFDerivAt.comp p.1
    (hasFDerivAt_prodMk_left p.1 p.2)).hasDerivAt
  exact hs.congr_deriv (alphaLambdaDeriv_eq_partialAlpha hD hG hj hp).symm

private theorem lambdaDeriv_one_at_one_eq_zero
    {V : Set ℝ} (hV : IsOpen V) {G : ℝ × ℝ → ℝ}
    (hGone : ∀ lambda ∈ V, G (1, lambda) = 0) {lambda : ℝ} (hlambda : lambda ∈ V) :
    lambdaDeriv G 1 1 lambda = 0 := by
  have heq : Filter.EventuallyEq (nhds lambda) (fun t : ℝ => G (1, t))
      (fun _ : ℝ => 0) := by
    filter_upwards [hV.mem_nhds hlambda] with t ht
    exact hGone t ht
  change deriv (fun t : ℝ => G (1, t)) lambda = 0
  rw [heq.deriv_eq]
  simp

private theorem lambdaDeriv_two_at_one_eq_zero
    {V : Set ℝ} (hV : IsOpen V) {G : ℝ × ℝ → ℝ}
    (hGone : ∀ lambda ∈ V, G (1, lambda) = 0) {lambda : ℝ} (hlambda : lambda ∈ V) :
    lambdaDeriv G 2 1 lambda = 0 := by
  have heq : Filter.EventuallyEq (nhds lambda)
      (fun t : ℝ => lambdaDeriv G 1 1 t) (fun _ : ℝ => 0) := by
    filter_upwards [hV.mem_nhds hlambda] with t ht
    exact lambdaDeriv_one_at_one_eq_zero hV hGone ht
  change deriv (fun t : ℝ => lambdaDeriv G 1 1 t) lambda = 0
  rw [heq.deriv_eq]
  simp

private theorem lambdaDeriv_at_one_eq_zero_of_le_two
    {V : Set ℝ} (hV : IsOpen V) {G : ℝ × ℝ → ℝ}
    (hGone : ∀ lambda ∈ V, G (1, lambda) = 0)
    {j : ℕ} (hj : j ≤ 2) {lambda : ℝ} (hlambda : lambda ∈ V) :
    lambdaDeriv G j 1 lambda = 0 := by
  interval_cases j
  · exact hGone lambda hlambda
  · exact lambdaDeriv_one_at_one_eq_zero hV hGone hlambda
  · exact lambdaDeriv_two_at_one_eq_zero hV hGone hlambda

private theorem alphaLambdaDeriv_zero_eq_partialAlpha
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) {p : ℝ × ℝ} (hp : p ∈ D) :
    alphaLambdaDeriv G 0 p.1 p.2 = partialAlpha G p := by
  simpa [lambdaDeriv] using
    (alphaLambdaDeriv_eq_partialAlpha hD hG (j := 0) (by norm_num) hp)

private theorem alphaLambdaDeriv_one_eq_partialAlpha_partialLambda
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) {p : ℝ × ℝ} (hp : p ∈ D) :
    alphaLambdaDeriv G 1 p.1 p.2 = partialAlpha (partialLambda G) p := by
  rw [alphaLambdaDeriv_eq_partialAlpha hD hG (j := 1) (by norm_num) hp]
  unfold partialAlpha
  have heq : Filter.EventuallyEq (nhds p)
      (fun q : ℝ × ℝ => lambdaDeriv G 1 q.1 q.2) (partialLambda G) := by
    filter_upwards [hD.mem_nhds hp] with q hq
    exact lambdaDeriv_one_eq_partialLambda hD (hG.of_le (by norm_num)) hq
  rw [heq.fderiv_eq]

private theorem alphaLambdaDeriv_two_eq_partialAlpha_partialLambda_two
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) {p : ℝ × ℝ} (hp : p ∈ D) :
    alphaLambdaDeriv G 2 p.1 p.2 =
      partialAlpha (partialLambda (partialLambda G)) p := by
  rw [alphaLambdaDeriv_eq_partialAlpha hD hG (j := 2) (by norm_num) hp]
  unfold partialAlpha
  have heq : Filter.EventuallyEq (nhds p)
      (fun q : ℝ × ℝ => lambdaDeriv G 2 q.1 q.2)
      (partialLambda (partialLambda G)) := by
    filter_upwards [hD.mem_nhds hp] with q hq
    exact lambdaDeriv_two_eq_partialLambda_two hD (hG.of_le (by norm_num)) hq
  rw [heq.fderiv_eq]

private theorem hasDerivAt_alphaLambdaDeriv_zero_snd
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) {p : ℝ × ℝ} (hp : p ∈ D) :
    HasDerivAt (fun lambda : ℝ => alphaLambdaDeriv G 0 p.1 lambda)
      (alphaLambdaDeriv G 1 p.1 p.2) p.2 := by
  have hbase := hasDerivAt_partialAlpha_snd hD (hG.of_le (by norm_num)) hp
  have hmem : Filter.Eventually (fun lambda : ℝ => (p.1, lambda) ∈ D) (nhds p.2) :=
    (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds (hD.mem_nhds hp)
  have heq : Filter.EventuallyEq (nhds p.2)
      (fun lambda : ℝ => alphaLambdaDeriv G 0 p.1 lambda)
      (fun lambda : ℝ => partialAlpha G (p.1, lambda)) := by
    filter_upwards [hmem] with lambda hlambda
    exact alphaLambdaDeriv_zero_eq_partialAlpha hD hG hlambda
  exact (hbase.congr_of_eventuallyEq heq).congr_deriv
    (alphaLambdaDeriv_one_eq_partialAlpha_partialLambda hD hG hp).symm

private theorem hasDerivAt_alphaLambdaDeriv_one_snd
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) {p : ℝ × ℝ} (hp : p ∈ D) :
    HasDerivAt (fun lambda : ℝ => alphaLambdaDeriv G 1 p.1 lambda)
      (alphaLambdaDeriv G 2 p.1 p.2) p.2 := by
  have hL : ContDiffOn ℝ 2 (partialLambda G) D :=
    contDiffOn_partialLambda_two hD hG
  have hbase := hasDerivAt_partialAlpha_snd hD hL hp
  have hmem : Filter.Eventually (fun lambda : ℝ => (p.1, lambda) ∈ D) (nhds p.2) :=
    (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds (hD.mem_nhds hp)
  have heq : Filter.EventuallyEq (nhds p.2)
      (fun lambda : ℝ => alphaLambdaDeriv G 1 p.1 lambda)
      (fun lambda : ℝ => partialAlpha (partialLambda G) (p.1, lambda)) := by
    filter_upwards [hmem] with lambda hlambda
    exact alphaLambdaDeriv_one_eq_partialAlpha_partialLambda hD hG hlambda
  exact (hbase.congr_of_eventuallyEq heq).congr_deriv
    (alphaLambdaDeriv_two_eq_partialAlpha_partialLambda_two hD hG hp).symm

private theorem removableShannonQuotient_eq_neg_integral_local
    (G : ℝ × ℝ → ℝ) {a lambda : ℝ} (hGone : G (1, lambda) = 0)
    (hcont : ContinuousOn (fun b => alphaLambdaDeriv G 0 b lambda) (uIcc 1 a))
    (hderiv : ∀ b ∈ uIcc (1 : ℝ) a,
      HasDerivAt (fun r => G (r, lambda))
        (alphaLambdaDeriv G 0 b lambda) b) :
    removableShannonQuotient G a lambda =
      -∫ s in (0 : ℝ)..1,
        alphaLambdaDeriv G 0 (1 + s * (a - 1)) lambda := by
  by_cases ha : a = 1
  · subst a
    simp [removableShannonQuotient]
  · rw [removableShannonQuotient_of_ne G ha]
    have hFTC : (∫ b in (1 : ℝ)..a, alphaLambdaDeriv G 0 b lambda) =
        G (a, lambda) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        hcont.intervalIntegrable, hGone, sub_zero]
    have haffine : ∀ s ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => 1 + t * (a - 1)) (a - 1) s := by
      intro s _hs
      simpa only [id_eq, one_mul, mul_comm] using
        ((hasDerivAt_id s).const_mul (a - 1)).const_add 1
    have himage : (fun s : ℝ => 1 + s * (a - 1)) '' uIcc (0 : ℝ) 1 ⊆
        uIcc (1 : ℝ) a := by
      rintro _ ⟨s, hs, rfl⟩
      have hs' : s ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le zero_le_one] using hs
      exact (convex_uIcc (1 : ℝ) a).add_smul_sub_mem
        left_mem_uIcc right_mem_uIcc hs'
    have hchange := intervalIntegral.integral_comp_mul_deriv'
      (a := (0 : ℝ)) (b := 1)
      (f := fun s : ℝ => 1 + s * (a - 1))
      (f' := fun _ => a - 1)
      (g := fun b => alphaLambdaDeriv G 0 b lambda)
      haffine continuous_const.continuousOn (hcont.mono himage)
    have hchange' : (∫ s in (0 : ℝ)..1,
        alphaLambdaDeriv G 0 (1 + s * (a - 1)) lambda * (a - 1)) =
        ∫ b in (1 : ℝ)..a, alphaLambdaDeriv G 0 b lambda := by
      simp only [Function.comp_apply, zero_mul, add_zero, one_mul] at hchange
      have hone : 1 + (a - 1) = a := by ring
      rw [hone] at hchange
      exact hchange
    have hfactor : (a - 1) *
        (∫ s in (0 : ℝ)..1,
          alphaLambdaDeriv G 0 (1 + s * (a - 1)) lambda) = G (a, lambda) := by
      rw [mul_comm, ← intervalIntegral.integral_mul_const]
      exact hchange'.trans hFTC
    rw [← hfactor]
    have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
    field_simp [hden]
    ring

private theorem lambdaDeriv_removable_one_of_ne
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) {p : ℝ × ℝ} (hp : p ∈ D) (ha : p.1 ≠ 1) :
    lambdaDeriv (fun q => removableShannonQuotient G q.1 q.2) 1 p.1 p.2 =
      removableShannonQuotient
        (fun q => lambdaDeriv G 1 q.1 q.2) p.1 p.2 := by
  have hGp : DifferentiableAt ℝ G p :=
    (((hG.of_le (by norm_num)) p hp).contDiffAt
      (hD.mem_nhds hp)).differentiableAt one_ne_zero
  have hs : DifferentiableAt ℝ (fun lambda : ℝ => G (p.1, lambda)) p.2 :=
    (hGp.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2).differentiableAt)
  have hd : HasDerivAt (fun lambda : ℝ => G (p.1, lambda) / (1 - p.1))
      (lambdaDeriv G 1 p.1 p.2 / (1 - p.1)) p.2 := by
    exact hs.hasDerivAt.div_const (1 - p.1)
  change deriv (fun lambda : ℝ => removableShannonQuotient G p.1 lambda) p.2 = _
  rw [show (fun lambda : ℝ => removableShannonQuotient G p.1 lambda) =
      (fun lambda : ℝ => G (p.1, lambda) / (1 - p.1)) by
        funext lambda
        exact removableShannonQuotient_of_ne G ha]
  rw [hd.deriv, removableShannonQuotient_of_ne _ ha]

private theorem lambdaDeriv_removable_two_of_ne
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) {p : ℝ × ℝ} (hp : p ∈ D) (ha : p.1 ≠ 1) :
    lambdaDeriv (fun q => removableShannonQuotient G q.1 q.2) 2 p.1 p.2 =
      removableShannonQuotient
        (fun q => lambdaDeriv G 2 q.1 q.2) p.1 p.2 := by
  let G1 : ℝ × ℝ → ℝ := fun q => lambdaDeriv G 1 q.1 q.2
  have hG1 := contDiffOn_lambdaDeriv_one_two hD hG
  have hG1p : DifferentiableAt ℝ G1 p :=
    (((hG1.of_le (by norm_num)) p hp).contDiffAt
      (hD.mem_nhds hp)).differentiableAt one_ne_zero
  have hs : DifferentiableAt ℝ (fun lambda : ℝ => G1 (p.1, lambda)) p.2 :=
    by
      simpa [Function.comp_def] using
        hG1p.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2).differentiableAt
  have hd : HasDerivAt (fun lambda : ℝ => G1 (p.1, lambda) / (1 - p.1))
      (lambdaDeriv G 2 p.1 p.2 / (1 - p.1)) p.2 := by
    exact hs.hasDerivAt.div_const (1 - p.1)
  have hmem : Filter.Eventually (fun lambda : ℝ => (p.1, lambda) ∈ D) (nhds p.2) :=
    (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds (hD.mem_nhds hp)
  have heq : Filter.EventuallyEq (nhds p.2)
      (fun lambda : ℝ =>
        lambdaDeriv (fun q => removableShannonQuotient G q.1 q.2) 1 p.1 lambda)
      (fun lambda : ℝ => G1 (p.1, lambda) / (1 - p.1)) := by
    filter_upwards [hmem] with lambda hlambda
    rw [lambdaDeriv_removable_one_of_ne hD hG hlambda ha,
      removableShannonQuotient_of_ne _ ha]
  change deriv (fun lambda : ℝ =>
    lambdaDeriv (fun q => removableShannonQuotient G q.1 q.2) 1 p.1 lambda) p.2 = _
  rw [heq.deriv_eq, hd.deriv, removableShannonQuotient_of_ne _ ha]

private theorem lambdaDeriv_removable_one_at_one
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) {lambda : ℝ} (hp : ((1 : ℝ), lambda) ∈ D) :
    lambdaDeriv (fun q => removableShannonQuotient G q.1 q.2) 1 1 lambda =
      removableShannonQuotient
        (fun q => lambdaDeriv G 1 q.1 q.2) 1 lambda := by
  have hmixed := hasDerivAt_alphaLambdaDeriv_zero_snd hD hG hp
  have hmixed' : HasDerivAt (fun t : ℝ => alphaLambdaDeriv G 0 1 t)
      (alphaLambdaDeriv G 1 1 lambda) lambda := by
    simpa using hmixed
  change deriv (fun t : ℝ => removableShannonQuotient G 1 t) lambda = _
  rw [show (fun t : ℝ => removableShannonQuotient G 1 t) =
      -(fun t : ℝ => alphaLambdaDeriv G 0 1 t) by
        funext t
        exact removableShannonQuotient_one G t]
  rw [hmixed'.neg.deriv, removableShannonQuotient_one]
  rfl

private theorem lambdaDeriv_removable_two_at_one
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) {lambda : ℝ} (hp : ((1 : ℝ), lambda) ∈ D) :
    lambdaDeriv (fun q => removableShannonQuotient G q.1 q.2) 2 1 lambda =
      removableShannonQuotient
        (fun q => lambdaDeriv G 2 q.1 q.2) 1 lambda := by
  have hmixed := hasDerivAt_alphaLambdaDeriv_one_snd hD hG hp
  have hmixed' : HasDerivAt (fun t : ℝ => alphaLambdaDeriv G 1 1 t)
      (alphaLambdaDeriv G 2 1 lambda) lambda := by
    simpa using hmixed
  have hmem : Filter.Eventually (fun t : ℝ => ((1 : ℝ), t) ∈ D) (nhds lambda) :=
    (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds (hD.mem_nhds hp)
  have heq : Filter.EventuallyEq (nhds lambda)
      (fun t : ℝ =>
        lambdaDeriv (fun q => removableShannonQuotient G q.1 q.2) 1 1 t)
      (-(fun t : ℝ => alphaLambdaDeriv G 1 1 t)) := by
    filter_upwards [hmem] with t ht
    rw [lambdaDeriv_removable_one_at_one hD hG ht,
      removableShannonQuotient_one]
    rfl
  change deriv (fun t : ℝ =>
    lambdaDeriv (fun q => removableShannonQuotient G q.1 q.2) 1 1 t) lambda = _
  rw [heq.deriv_eq, hmixed'.neg.deriv, removableShannonQuotient_one]
  rfl

private theorem lambdaDeriv_removable_commute_of_le_two
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {G : ℝ × ℝ → ℝ}
    (hG : ContDiffOn ℝ 3 G D) {j : ℕ} (hj : j ≤ 2)
    {p : ℝ × ℝ} (hp : p ∈ D) :
    lambdaDeriv (fun q => removableShannonQuotient G q.1 q.2) j p.1 p.2 =
      removableShannonQuotient
        (fun q => lambdaDeriv G j q.1 q.2) p.1 p.2 := by
  interval_cases j
  · rfl
  · by_cases ha : p.1 = 1
    · have hp' : ((1 : ℝ), p.2) ∈ D := by
        simpa [← ha] using hp
      simpa [ha] using lambdaDeriv_removable_one_at_one hD hG hp'
    · exact lambdaDeriv_removable_one_of_ne hD hG hp ha
  · by_cases ha : p.1 = 1
    · have hp' : ((1 : ℝ), p.2) ∈ D := by
        simpa [← ha] using hp
      simpa [ha] using lambdaDeriv_removable_two_at_one hD hG hp'
    · exact lambdaDeriv_removable_two_of_ne hD hG hp ha

private theorem continuousOn_neg_intervalIntegral
    (A : ℝ × ℝ → ℝ) {D S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (hA : ContinuousOn A D)
    (hsegment : ∀ (s : ℝ), s ∈ Icc (0 : ℝ) 1 → ∀ p ∈ S,
      (1 + s * (p.1 - 1), p.2) ∈ D) :
    ContinuousOn (fun p : ℝ × ℝ =>
      -∫ s in (0 : ℝ)..1, A (1 + s * (p.1 - 1), p.2)) S := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let T := Set.Icc (0 : ℝ) 1
  letI : MeasureSpace T := Measure.Subtype.measureSpace
  letI : IsProbabilityMeasure (volume : Measure T) := {
    measure_univ := by
      dsimp only [T]
      rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc,
        Real.volume_Icc, sub_zero, ENNReal.ofReal_one] }
  let K : C(T × S, ℝ) :=
    ⟨fun z => A (1 + z.1.1 * (z.2.1.1 - 1), z.2.1.2), by
      have hc : Continuous (fun z : T × S =>
          ((1 + z.1.1 * (z.2.1.1 - 1), z.2.1.2) : ℝ × ℝ)) := by
        fun_prop
      exact hA.comp_continuous hc fun z =>
        hsegment z.1.1 z.1.2 z.2.1 z.2.2⟩
  have hKint : Integrable (K.curry : T → C(S, ℝ)) :=
    K.curry.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.intro isCompact_univ fun x hx =>
        (hx (Set.mem_univ x)).elim)
  let H : C(S, ℝ) := ∫ s : T, K.curry s
  have hHapply (p : S) : H p =
      ∫ s in (0 : ℝ)..1, A (1 + s * (p.1.1 - 1), p.1.2) := by
    change (∫ s : T, K.curry s) p = _
    rw [ContinuousMap.integral_apply hKint p]
    change (∫ s : T, A (1 + s.1 * (p.1.1 - 1), p.1.2)) = _
    dsimp only [T]
    calc
      (∫ s : Set.Icc (0 : ℝ) 1,
          A (1 + s.1 * (p.1.1 - 1), p.1.2)) =
          ∫ s in Set.Icc (0 : ℝ) 1,
            A (1 + s * (p.1.1 - 1), p.1.2) := by
        change (∫ s : Set.Icc (0 : ℝ) 1,
          A (1 + s.1 * (p.1.1 - 1), p.1.2)
            ∂Measure.comap Subtype.val volume) = _
        exact MeasureTheory.integral_subtype_comap (μ := volume)
          (show MeasurableSet (Set.Icc (0 : ℝ) 1) from measurableSet_Icc)
          (fun s : ℝ => A (1 + s * (p.1.1 - 1), p.1.2))
      _ = ∫ s in Set.Ioc (0 : ℝ) 1,
            A (1 + s * (p.1.1 - 1), p.1.2) := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      _ = ∫ s in (0 : ℝ)..1,
            A (1 + s * (p.1.1 - 1), p.1.2) := by
        rw [← intervalIntegral.integral_of_le zero_le_one]
  rw [continuousOn_iff_continuous_restrict]
  have heq : S.restrict (fun p : ℝ × ℝ =>
      -∫ s in (0 : ℝ)..1, A (1 + s * (p.1 - 1), p.2)) =
      fun p => -H p := by
    funext p
    change -(∫ s in (0 : ℝ)..1,
      A (1 + s * (p.1.1 - 1), p.1.2)) = -H p
    rw [hHapply]
  rw [heq]
  exact H.continuous.neg

/-- Parameterized removable quotient at the Shannon point.

The mixed derivatives at `a = 1` are consequences of the stated finite
`C^3` regularity; no commutation assumption is added to the theorem. -/
theorem parameterizedRemovableShannonQuotient
    {c d : ℝ} (hcd : c ≤ d) {U V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (h1 : (1 : ℝ) ∈ U)
    (hcdV : Icc c d ⊆ V) (F : ℝ × ℝ → ℝ)
    (hF : ContDiffOn ℝ 3 F (U ×ˢ V))
    (hF1 : ∀ lambda ∈ V, F (1, lambda) = 0) :
    ∃ eps : ℝ, 0 < eps ∧
      let S := Icc (1 - eps) (1 + eps) ×ˢ Icc c d
      S ⊆ U ×ˢ V ∧
      ∀ j : ℕ, j ≤ 2 →
        ContinuousOn (fun p : ℝ × ℝ =>
          lambdaDeriv (fun q => removableShannonQuotient F q.1 q.2)
            j p.1 p.2) S ∧
        ∀ p : ℝ × ℝ, p ∈ S →
          lambdaDeriv (fun q => removableShannonQuotient F q.1 q.2)
              j p.1 p.2 =
            -∫ s in (0 : ℝ)..1,
              alphaLambdaDeriv F j (1 + s * (p.1 - 1)) p.2 := by
  have _hcd : c ≤ d := hcd
  have hD : IsOpen (U ×ˢ V) := hU.prod hV
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU 1 h1
  let eps : ℝ := r / 2
  have heps : 0 < eps := by
    dsimp only [eps]
    positivity
  have hIccU : Icc (1 - eps) (1 + eps) ⊆ U := by
    intro a ha
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |a - 1| ≤ eps := by
      rw [abs_le]
      constructor <;> linarith [ha.1, ha.2]
    exact habs.trans_lt (by dsimp only [eps]; linarith)
  let S : Set (ℝ × ℝ) := Icc (1 - eps) (1 + eps) ×ˢ Icc c d
  have hSsub : S ⊆ U ×ˢ V := by
    rintro p ⟨ha, hlambda⟩
    exact ⟨hIccU ha, hcdV hlambda⟩
  have hScompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hOneIcc : (1 : ℝ) ∈ Icc (1 - eps) (1 + eps) := by
    constructor <;> linarith
  have hsegment : ∀ (s : ℝ), s ∈ Icc (0 : ℝ) 1 → ∀ p ∈ S,
      (1 + s * (p.1 - 1), p.2) ∈ U ×ˢ V := by
    intro s hs p hp
    apply hSsub
    exact ⟨(convex_Icc (1 - eps) (1 + eps)).add_smul_sub_mem
      hOneIcc hp.1 hs, hp.2⟩
  refine ⟨eps, heps, ?_⟩
  change S ⊆ U ×ˢ V ∧ _
  refine ⟨hSsub, ?_⟩
  intro j hj
  let Fj : ℝ × ℝ → ℝ := fun q => lambdaDeriv F j q.1 q.2
  have hMixed : ContinuousOn
      (fun q : ℝ × ℝ => alphaLambdaDeriv F j q.1 q.2) (U ×ˢ V) :=
    (contDiffOn_alphaLambdaDeriv hD hF hj).continuousOn
  have hformula : ∀ p ∈ S,
      lambdaDeriv (fun q => removableShannonQuotient F q.1 q.2) j p.1 p.2 =
        -∫ s in (0 : ℝ)..1,
          alphaLambdaDeriv F j (1 + s * (p.1 - 1)) p.2 := by
    intro p hp
    rw [lambdaDeriv_removable_commute_of_le_two hD hF hj (hSsub hp)]
    change removableShannonQuotient Fj p.1 p.2 = _
    apply removableShannonQuotient_eq_neg_integral_local Fj
    · exact lambdaDeriv_at_one_eq_zero_of_le_two hV hF1 hj (hcdV hp.2)
    · have hsegIcc : uIcc (1 : ℝ) p.1 ⊆ Icc (1 - eps) (1 + eps) :=
        uIcc_subset_Icc hOneIcc hp.1
      exact hMixed.comp (continuousOn_id.prodMk continuousOn_const) fun b hb =>
        hSsub ⟨hsegIcc hb, hp.2⟩
    · intro b hb
      have hsegIcc : uIcc (1 : ℝ) p.1 ⊆ Icc (1 - eps) (1 + eps) :=
        uIcc_subset_Icc hOneIcc hp.1
      have hbS : (b, p.2) ∈ S := ⟨hsegIcc hb, hp.2⟩
      exact hasDerivAt_lambdaDeriv_fst hD hF hj
        (hSsub hbS)
  constructor
  · have hInt := continuousOn_neg_intervalIntegral
      (fun q : ℝ × ℝ => alphaLambdaDeriv F j q.1 q.2)
      hScompact hMixed hsegment
    exact hInt.congr hformula
  · exact hformula

end ConditionalEntropy
