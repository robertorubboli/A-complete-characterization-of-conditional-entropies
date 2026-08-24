import ConditionalEntropy.NullThresholds

/-!
# Support-set algebra for necessity

These lemmas isolate the order-topological bookkeeping common to the negative
temperate and negative tropical branches.
-/

noncomputable section

open MeasureTheory Set

namespace ConditionalEntropy

/-- Strengthened support dichotomy retaining membership of the exceptional
upper point. -/
theorem supportLowerOrUniqueUpperWithMem (rho : Measure Param)
    (hsub : (suppMeasure rho ∩ Ioi (1 : Param)).Subsingleton) :
    suppMeasure rho ⊆ Icc (0 : Param) 1 ∨
      ∃ astar : Param, astar ∈ suppMeasure rho ∧ 1 < astar ∧
        suppMeasure rho ⊆ Icc (0 : Param) 1 ∪ {astar} := by
  by_cases hlower : suppMeasure rho ⊆ Icc (0 : Param) 1
  · exact Or.inl hlower
  · right
    obtain ⟨astar, hastarSupp, hastarLower⟩ := Set.not_subset.mp hlower
    have hastar : (1 : Param) < astar := by
      have hzero : (0 : Param) ≤ astar := bot_le
      exact lt_of_not_ge (fun hle ↦ hastarLower ⟨hzero, hle⟩)
    refine ⟨astar, hastarSupp, hastar, ?_⟩
    intro beta hbeta
    by_cases hbetaOne : beta ≤ (1 : Param)
    · exact Or.inl ⟨bot_le, hbetaOne⟩
    · right
      have heq : beta = astar := hsub
        ⟨hbeta, lt_of_not_ge hbetaOne⟩ ⟨hastarSupp, hastar⟩
      simp [heq]

/-- If the part of a support above one is subsingleton, then either there is
no such point or the whole support is contained in the lower interval plus
that unique exceptional point. -/
theorem supportLowerOrUniqueUpper (rho : Measure Param)
    (hsub : (suppMeasure rho ∩ Ioi (1 : Param)).Subsingleton) :
    suppMeasure rho ⊆ Icc (0 : Param) 1 ∨
      ∃ astar : Param, 1 < astar ∧
        suppMeasure rho ⊆ Icc (0 : Param) 1 ∪ {astar} := by
  rcases supportLowerOrUniqueUpperWithMem rho hsub with hlower |
      ⟨astar, _hastarSupp, hastar, hsupp⟩
  · exact Or.inl hlower
  · exact Or.inr ⟨astar, hastar, hsupp⟩

/-- Every upper parameter strictly above one admits a finite real null
threshold strictly between one and that parameter.  This uniform statement
also covers the compactified endpoint. -/
theorem exists_real_null_between_one_upper (rho : Measure Param)
    [IsFiniteMeasure rho] {astar : Param} (hastar : (1 : Param) < astar) :
    ∃ b : ℝ, 1 < b ∧ finiteParam b < astar ∧
      rho ({finiteParam b} : Set Param) = 0 := by
  obtain ⟨x, hx, hnull⟩ := exists_null_atom_mem_open rho isOpen_Ioo
    (nonempty_Ioo.mpr hastar)
  have hxTop : x ≠ (⊤ : Param) := ne_top_of_lt (hx.2.trans_le le_top)
  let b : ℝ := ENNReal.toReal x
  have hback : finiteParam b = x := by
    simpa only [b, paramToReal] using finiteParam_paramToReal x hxTop
  have hb0 : 0 < b := by
    have hxZero : x ≠ (0 : Param) := by
      have hzeroOne : (0 : Param) < 1 := by norm_num
      exact ne_of_gt (hzeroOne.trans hx.1)
    exact ENNReal.toReal_pos hxZero hxTop
  have hb : 1 < b := by
    have hparam : finiteParam (1 : ℝ) < finiteParam b := by
      rw [hback, finiteParam_one]
      exact hx.1
    change ENNReal.ofReal 1 < ENNReal.ofReal b at hparam
    exact (ENNReal.ofReal_lt_ofReal_iff hb0).mp hparam
  exact ⟨b, hb, by simpa only [hback] using hx.2,
    by simpa only [hback] using hnull⟩

end ConditionalEntropy
