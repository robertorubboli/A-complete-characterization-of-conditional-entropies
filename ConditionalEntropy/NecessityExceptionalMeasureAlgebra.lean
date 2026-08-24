import ConditionalEntropy.NecessityMeasureAlgebra
import ConditionalEntropy.NecessitySupportAlgebra

/-!
# Measure algebra for the unique-upper-support necessity branch

If a finite parameter measure is supported on the closed lower interval and
one exceptional point above order one, its entire upper singular moment is
carried by that point.  This file records the resulting finiteness, truncation,
and isolation identities used in the exceptional necessity arguments.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace ConditionalEntropy

/-- A support inclusion may be used as an almost-everywhere membership
statement. -/
theorem ae_mem_of_suppMeasure_subset {rho : Measure Param} {s : Set Param}
    (hsupp : suppMeasure rho ⊆ s) : ∀ᵐ a ∂rho, a ∈ s := by
  filter_upwards [Measure.support_mem_ae] with a ha
  exact hsupp ha

/-- Above any cutoff lying between one and the exceptional point, the whole
tail measure is exactly the exceptional singleton mass. -/
theorem exceptionalUpperTail_eq_singleton {rho : Measure Param}
    {astar c : Param} (_hastar : (1 : Param) < astar)
    (hsupp : suppMeasure rho ⊆ Icc (0 : Param) 1 ∪ {astar})
    (hc1 : (1 : Param) ≤ c) (hcstar : c < astar) :
    rho (Ioi c) = rho ({astar} : Set Param) := by
  apply measure_congr
  filter_upwards [ae_mem_of_suppMeasure_subset hsupp] with a ha
  apply propext
  change (c < a ↔ a = astar)
  constructor
  · intro hca
    rcases ha with hlow | hexc
    · exact False.elim <| (not_lt_of_ge (hlow.2.trans hc1)) hca
    · simpa only [Set.mem_singleton_iff] using hexc
  · intro haeq
    subst a
    exact hcstar

/-- Real-cutoff specialization of `exceptionalUpperTail_eq_singleton`. -/
theorem exceptionalUpperTail_finiteParam_eq_singleton
    {rho : Measure Param} {astar : Param} (hastar : (1 : Param) < astar)
    (hsupp : suppMeasure rho ⊆ Icc (0 : Param) 1 ∪ {astar})
    {b : ℝ} (hb : 1 < b) (hbastar : finiteParam b < astar) :
    rho (Ioi (finiteParam b)) = rho ({astar} : Set Param) := by
  have hbParam : (1 : Param) ≤ finiteParam b := by
    rw [← finiteParam_one]
    change ENNReal.ofReal 1 ≤ ENNReal.ofReal b
    exact ENNReal.ofReal_le_ofReal hb.le
  exact exceptionalUpperTail_eq_singleton hastar hsupp hbParam hbastar

/-- If the exceptional point belongs to the support, it is the entire support
above one and hence is isolated there. -/
theorem exceptionalSupport_inter_Ioi_eq_singleton {rho : Measure Param}
    {astar : Param} (hastar : (1 : Param) < astar)
    (hsupp : suppMeasure rho ⊆ Icc (0 : Param) 1 ∪ {astar})
    (hastarSupp : astar ∈ suppMeasure rho) :
    suppMeasure rho ∩ Ioi (1 : Param) = ({astar} : Set Param) := by
  ext a
  constructor
  · rintro ⟨haSupp, ha1⟩
    rcases hsupp haSupp with hlow | hexc
    · exact False.elim <| (not_lt_of_ge hlow.2) ha1
    · exact hexc
  · intro ha
    have haeq : a = astar := Set.mem_singleton_iff.mp ha
    subst a
    exact ⟨hastarSupp, hastar⟩

/-- An exceptional point which lies in the support has strictly positive
singleton mass. -/
theorem exceptionalAtom_pos_of_mem_support {rho : Measure Param}
    {astar : Param} (hastar : (1 : Param) < astar)
    (hsupp : suppMeasure rho ⊆ Icc (0 : Param) 1 ∪ {astar})
    (hastarSupp : astar ∈ suppMeasure rho) :
    0 < rho ({astar} : Set Param) := by
  have htail : 0 < rho (Ioi (1 : Param)) :=
    measure_pos_of_mem_support_open hastarSupp isOpen_Ioi hastar
  rw [exceptionalUpperTail_eq_singleton hastar hsupp le_rfl hastar] at htail
  exact htail

/-- Under exceptional support, the upper extended moment is exactly the upper
kernel at the exceptional point times its singleton mass. -/
theorem MUpper_eq_exceptionalAtom {rho : Measure Param}
    {astar : Param} (hastar : (1 : Param) < astar)
    (hsupp : suppMeasure rho ⊆ Icc (0 : Param) 1 ∪ {astar}) :
    MUpper rho = omegaUpper astar * rho ({astar} : Set Param) := by
  have hae : ∀ᵐ a ∂rho, omegaUpper a =
      ({astar} : Set Param).indicator (fun _ ↦ omegaUpper astar) a := by
    filter_upwards [Measure.support_mem_ae] with a ha
    rcases hsupp ha with hlow | hexc
    · have hnotUpper : a ∉ Ioi (1 : Param) := not_lt_of_ge hlow.2
      have hne : a ≠ astar := ne_of_lt (hlow.2.trans_lt hastar)
      have homega : omegaUpper a = 0 := by
        unfold omegaUpper
        rw [if_neg hnotUpper]
      simp [homega, hne]
    · have haeq : a = astar := Set.mem_singleton_iff.mp hexc
      subst a
      simp
  calc
    MUpper rho = ∫⁻ a, omegaUpper a ∂rho := rfl
    _ = ∫⁻ a, ({astar} : Set Param).indicator
        (fun _ ↦ omegaUpper astar) a ∂rho := lintegral_congr_ae hae
    _ = omegaUpper astar * rho ({astar} : Set Param) := by
      rw [lintegral_indicator (measurableSet_singleton astar),
        setLIntegral_const]

/-- The unique-upper-support hypothesis makes the full upper moment finite. -/
theorem MUpper_lt_top_of_exceptional_support (nu : FiniteMeasure Param)
    {astar : Param} (hastar : (1 : Param) < astar)
    (hsupp : suppMeasure (finiteMeasure nu) ⊆
      Icc (0 : Param) 1 ∪ {astar}) :
    MUpper (finiteMeasure nu) < ⊤ := by
  letI : IsFiniteMeasure (finiteMeasure nu) := by
    unfold finiteMeasure
    infer_instance
  rw [MUpper_eq_exceptionalAtom hastar hsupp]
  exact ENNReal.mul_lt_top (omegaUpper_lt_top astar)
    (measure_lt_top (finiteMeasure nu) _)

private theorem toReal_omegaUpper_of_exceptional {a : Param}
    (ha : (1 : Param) < a) :
    ENNReal.toReal (omegaUpper a) = -singularWeight a := by
  unfold omegaUpper
  rw [if_pos (show a ∈ Ioi (1 : Param) from ha), ENNReal.toReal_ofReal]
  exact neg_nonneg.mpr (singularWeight_neg_of_one_lt ha).le

/-- A truncation below the exceptional point already contains the whole upper
moment. -/
theorem upperTrunc_eq_MUpper_toReal_of_exceptional_support
    (nu : FiniteMeasure Param) {astar : Param}
    (hastar : (1 : Param) < astar)
    (hsupp : suppMeasure (finiteMeasure nu) ⊆
      Icc (0 : Param) 1 ∪ {astar})
    {b : ℝ} (hb : 1 < b) (hbastar : finiteParam b < astar) :
    upperTrunc nu b = ENNReal.toReal (MUpper (finiteMeasure nu)) := by
  let rho : Measure Param := finiteMeasure nu
  have hbParam : (1 : Param) < finiteParam b := by
    rw [← finiteParam_one]
    change ENNReal.ofReal 1 < ENNReal.ofReal b
    exact (ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans hb)).2 hb
  have hae : ∀ᵐ a ∂rho,
      (Ioi (finiteParam b)).indicator (fun beta ↦ -singularWeight beta) a =
        ENNReal.toReal (omegaUpper a) := by
    filter_upwards [Measure.support_mem_ae] with a ha
    rcases hsupp ha with hlow | hexc
    · have hnotTail : a ∉ Ioi (finiteParam b) :=
        not_lt_of_ge (hlow.2.trans hbParam.le)
      have hnotUpper : a ∉ Ioi (1 : Param) := not_lt_of_ge hlow.2
      have homega : omegaUpper a = 0 := by
        unfold omegaUpper
        rw [if_neg hnotUpper]
      simp [hnotTail, homega]
    · have haeq : a = astar := Set.mem_singleton_iff.mp hexc
      subst a
      have hmem : astar ∈ Ioi (finiteParam b) := hbastar
      rw [Set.indicator_of_mem hmem]
      exact (toReal_omegaUpper_of_exceptional hastar).symm
  calc
    upperTrunc nu b = ∫ a,
        (Ioi (finiteParam b)).indicator
          (fun beta ↦ -singularWeight beta) a ∂rho := by
      rw [upperTrunc]
      exact (integral_indicator measurableSet_Ioi).symm
    _ = ∫ a, ENNReal.toReal (omegaUpper a) ∂rho :=
      integral_congr_ae hae
    _ = ENNReal.toReal (∫⁻ a, omegaUpper a ∂rho) :=
      integral_toReal measurable_omegaUpper.aemeasurable
        (ae_of_all _ fun a ↦ omegaUpper_lt_top a)
    _ = ENNReal.toReal (MUpper (finiteMeasure nu)) := rfl

/-- When the exceptional point is present in the support, every admissible
upper truncation below it is strictly positive. -/
theorem upperTrunc_pos_of_exceptional_mem_support
    (nu : FiniteMeasure Param) {astar : Param}
    (hastar : (1 : Param) < astar)
    (hsupp : suppMeasure (finiteMeasure nu) ⊆
      Icc (0 : Param) 1 ∪ {astar})
    (hastarSupp : astar ∈ suppMeasure (finiteMeasure nu))
    {b : ℝ} (hb : 1 < b) (hbastar : finiteParam b < astar) :
    0 < upperTrunc nu b := by
  have hatom : 0 < finiteMeasure nu ({astar} : Set Param) :=
    exceptionalAtom_pos_of_mem_support hastar hsupp hastarSupp
  have homega : 0 < omegaUpper astar := by
    unfold omegaUpper
    rw [if_pos (show astar ∈ Ioi (1 : Param) from hastar)]
    exact ENNReal.ofReal_pos.mpr
      (neg_pos.mpr (singularWeight_neg_of_one_lt hastar))
  have hMpos : 0 < MUpper (finiteMeasure nu) := by
    rw [MUpper_eq_exceptionalAtom hastar hsupp]
    exact ENNReal.mul_pos homega.ne' hatom.ne'
  have hMtop : MUpper (finiteMeasure nu) ≠ ⊤ :=
    (MUpper_lt_top_of_exceptional_support nu hastar hsupp).ne
  rw [upperTrunc_eq_MUpper_toReal_of_exceptional_support
    nu hastar hsupp hb hbastar]
  exact ENNReal.toReal_pos hMpos.ne' hMtop

/-- The complete upper-measure package used by the exceptional branch. -/
theorem exceptionalUpperMeasurePackage
    (nu : FiniteMeasure Param) {astar : Param}
    (hastar : (1 : Param) < astar)
    (hsupp : suppMeasure (finiteMeasure nu) ⊆
      Icc (0 : Param) 1 ∪ {astar})
    {b : ℝ} (hb : 1 < b) (hbastar : finiteParam b < astar) :
    MUpper (finiteMeasure nu) < ⊤ ∧
      upperTrunc nu b = ENNReal.toReal (MUpper (finiteMeasure nu)) ∧
      finiteMeasure nu (Ioi (finiteParam b)) =
        finiteMeasure nu ({astar} : Set Param) ∧
      (astar ∈ suppMeasure (finiteMeasure nu) →
        0 < finiteMeasure nu ({astar} : Set Param)) := by
  exact ⟨MUpper_lt_top_of_exceptional_support nu hastar hsupp,
    upperTrunc_eq_MUpper_toReal_of_exceptional_support
      nu hastar hsupp hb hbastar,
    exceptionalUpperTail_finiteParam_eq_singleton
      hastar hsupp hb hbastar,
    exceptionalAtom_pos_of_mem_support hastar hsupp⟩

end ConditionalEntropy
