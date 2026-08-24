import ConditionalEntropy.BlockLocalizationInterfaces
import ConditionalEntropy.CompactUniformBridge
import ConditionalEntropy.CurvatureObstructions

/-!
# Stationarity packages from block localization

The norm-free first block kernel is bundled as a continuous linear functional.
Together with the compact-uniform first- and second-kernel limits, this gives
the exact stationarity package used by the corrected quasi-convexity
obstruction.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ConditionalEntropy

/-- The first norm-free kernel of a finite block model, bundled as a
continuous linear functional of its velocity. -/
def blockGFirstCLM {J : ℕ} (mu : SignedMeasure Param)
    (B : BlockData J) (n : ℕ) (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop) :
    (Fin (J + 1) → ℝ) →L[ℝ] ℝ where
  toFun u := blockGKernel mu B n u 1
  map_add' u v := (blockKernelRegularity mu B jTop hTop n).1 u v
  map_smul' c u := by
    simpa [smul_eq_mul] using
      (blockKernelRegularity mu B jTop hTop n).2.1 c u
  cont := (blockKernelRegularity mu B jTop hTop n).2.2.1

@[simp] theorem blockGFirstCLM_apply {J : ℕ}
    (mu : SignedMeasure Param) (B : BlockData J) (n : ℕ)
    (jTop : Fin (J + 1))
    (hTop : ∀ j : Fin (J + 1), j ≠ jTop → B.a j < B.a jTop)
    (u : Fin (J + 1) → ℝ) :
    blockGFirstCLM mu B n jTop hTop u = blockGKernel mu B n u 1 := rfl

/-- The limiting first three-block kernel, bundled as a continuous linear
functional of the limiting velocity. -/
def threeGFirstCLM (mu : SignedMeasure Param) (a b : ℝ) :
    (Fin 3 → ℝ) →L[ℝ] ℝ where
  toFun u := threeGFirst mu a b u
  map_add' u v := by
    unfold threeGFirst
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  map_smul' c u := by
    unfold threeGFirst
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring_nf
  cont := continuous_threeGFirst mu a b

@[simp] theorem threeGFirstCLM_apply
    (mu : SignedMeasure Param) (a b : ℝ) (u : Fin 3 → ℝ) :
    threeGFirstCLM mu a b u = threeGFirst mu a b u := rfl

/-- Three-block norm-free localization, kernel regularity, and limiting
continuity assembled into the exact corrected-stationarity interface. -/
theorem threeBlockGStationarityPackage
    (mu : SignedMeasure Param) (a b R : ℝ)
    (ha : 0 < a) (hab : a < b) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hR : a + b < R)
    (hmu : signedTV mu ({finiteParam a} : Set Param) = 0 ∧
      signedTV mu ({finiteParam b} : Set Param) = 0) :
    let B := threeBlockData a b R ha hab hR
    StationarityPackage
      (fun n ↦ blockGFirstCLM mu B n 2
        (threeBlockTopUnique a b R ha hab hR))
      (threeGFirstCLM mu a b)
      (fun n u ↦ blockGKernel mu B n u 2)
      (threeGSecond mu a b) := by
  dsimp only
  let B := threeBlockData a b R ha hab hR
  let hTop := threeBlockTopUnique a b R ha hab hR
  refine {
    bN_continuous := ?_
    b_continuous := continuous_threeGSecond mu a b
    aN_compactUniform := ?_
    bN_compactUniform := ?_
  }
  · intro n
    exact (blockKernelRegularity mu B 2 hTop n).2.2.2
  · intro K hK hK0
    have Hloc := threeBlockLocalization mu a b R ha hab ha1 hb1 hR
      K hK0 hK hmu
    dsimp only at Hloc
    have ht : TendstoUniformlyOn
        (fun n u ↦ blockGKernel mu B n u 1)
        (threeGFirst mu a b) atTop K :=
      compactUniformConverges_tendstoUniformlyOn K hK0 hK
        (fun n u ↦ blockGKernel mu B n u 1)
        (threeGFirst mu a b)
        (fun n ↦ ((blockKernelRegularity mu B 2 hTop n).2.2.1).continuousOn)
        (continuous_threeGFirst mu a b).continuousOn Hloc.2.2.1
    change TendstoUniformlyOn
      (fun n u ↦ blockGKernel mu B n u 1)
      (threeGFirst mu a b) atTop K
    exact ht
  · intro K hK hK0
    have Hloc := threeBlockLocalization mu a b R ha hab ha1 hb1 hR
      K hK0 hK hmu
    dsimp only at Hloc
    exact compactUniformConverges_tendstoUniformlyOn K hK0 hK
      (fun n u ↦ blockGKernel mu B n u 2)
      (threeGSecond mu a b)
      (fun n ↦ ((blockKernelRegularity mu B 2 hTop n).2.2.2).continuousOn)
      (continuous_threeGSecond mu a b).continuousOn Hloc.2.2.2

end ConditionalEntropy
