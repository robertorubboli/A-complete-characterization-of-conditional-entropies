# Declaration-level dependency index

This is the source-of-truth declaration-level audit underlying the manuscript
correspondence table. Each row names exactly one checked Lean theorem. “Direct
checked dependencies” lists only project declarations invoked by its proof;
Mathlib lemmas and definitions are not expanded. A dash therefore means a
project leaf, not a proof that uses no Mathlib results.

The boxes and arrows in `dependency-graph.dot` give an eleven-layer condensed
view of the intended development; they are not one box per statement. The
exhaustive 152-row statement mapping is in `BLUEPRINT_STATEMENT_STATUS.md` and
`blueprint-statement-correspondence.tex`. This file separately records the
checked declaration-to-declaration dependencies.

## Section 4: proof-carrying cone interface

| Lean theorem | Direct checked dependencies |
|---|---|
| `originExtension` | — |
| `puncturedConeConvex` | — |
| `compositionRule` | — |
| `coneCompositionRule` | — |

## Appendix A: one-column shape and conditioning

| Lean theorem | Direct checked dependencies |
|---|---|
| `isSuperadditive_of_concave_posHomogeneous` | — |
| `isSubadditive_of_convex_posHomogeneous` | — |
| `superadditive_finset_sum` | — |
| `subadditive_finset_sum` | — |
| `columnLift_pushConditioning_ge` | `superadditive_finset_sum` |
| `columnLift_pushConditioning_le` | `subadditive_finset_sum` |
| `conditioning_monotone_of_concave` | `isSuperadditive_of_concave_posHomogeneous`, `columnLift_pushConditioning_ge` |
| `conditioning_antitone_of_convex` | `isSubadditive_of_convex_posHomogeneous`, `columnLift_pushConditioning_le` |

## Section 4: coefficient curvature and sufficiency

| Lean theorem | Direct checked dependencies |
|---|---|
| `monomialCurvature_eq_neg_variance` | — |
| `monomialCurvature_nonpos_of_nonneg` | `monomialCurvature_eq_neg_variance` |
| `coefficient_mem_Icc_of_curvature_nonpos` | — |
| `monomialCurvature_pos_of_negative_coefficient` | — |
| `positiveTemperate_coefficients_nonnegative` | `monomialCurvature_nonpos_of_nonneg` |
| `negativeTemperate_two_coefficient_curvature` | — |
| `derivation_supported_below_has_no_upper_obstruction` | — |

## Section 5: scalar obstructions and necessity

| Lean theorem | Direct checked dependencies |
|---|---|
| `two_positive_stationary_witness` | — |
| `negative_tail_concavity_obstruction` | — |
| `excessive_lower_moment_concavity_obstruction` | — |
| `shannon_atom_concavity_obstruction` | — |
| `positive_tail_derivation_obstruction` | — |
| `positiveTemperate_shannon_atom_zero` | `shannon_atom_concavity_obstruction` |
| `positiveTemperate_no_upper_moment` | `negative_tail_concavity_obstruction` |
| `positiveTemperate_lowerMoment_le_one` | `excessive_lower_moment_concavity_obstruction` |
| `negativeTemperate_truncated_moment` | `two_positive_stationary_witness` |
| `negativeTemperate_atMostOneUpperCell` | `two_positive_stationary_witness` |
| `negativeTropical_moment_nonnegative` | `two_positive_stationary_witness` |
| `derivation_no_positive_upper_tail` | `positive_tail_derivation_obstruction` |
| `positiveTemperate_necessary` | `positiveTemperate_shannon_atom_zero`, `positiveTemperate_no_upper_moment`, `positiveTemperate_lowerMoment_le_one` |
| `negativeTemperate_exceptional_moment` | `negativeTemperate_truncated_moment` |
| `negativeTropical_exceptional_moment` | `negativeTropical_moment_nonnegative` |
| `derivation_necessary` | `derivation_no_positive_upper_tail` |

## Checked boundary declarations

These declarations are checked but not connected to a paper-facing conclusion
by a solid edge. The intervening two-block, three-block, Shannon-point
localization and differentiation-under-the-integral arguments have not yet
been formalized.

| Lean theorem | Direct checked dependencies |
|---|---|
| `stationarityCorrection_dot` | — |
| `stationarityCorrection_tendsto` | — |
| `not_concave_of_strict_midpoint_valley` | — |
| `not_convex_of_strict_midpoint_peak` | — |
| `not_quasiConvex_of_strict_midpoint_peak` | — |
| `dominantBlock_first` | — |
| `dominantBlock_second` | — |

## Appendix B.7: pointwise limits preserve shape

| Lean theorem | Direct checked dependencies |
|---|---|
| `isConcave_of_pointwise_tendsto` | — |
| `isConvex_of_pointwise_tendsto` | — |
| `isQuasiConvex_of_pointwise_tendsto` | — |
| `isStronglyQuasiConcave_of_pointwise_tendsto` | — |

## Closed audit certificate

| Lean theorem | Direct checked dependencies |
|---|---|
| `verifiedKernelBundle` | the twenty boundary declarations appearing as its universally quantified conjuncts |

The seven groups contain 4, 8, 7, 16, 7, 4, and 1 declarations, respectively,
for a total of **47 public checked theorem/lemma declarations**. The six private
algebraic helpers used internally by the B.12 proof are intentionally excluded
from this public correspondence count. The first three declarations
in the final group correspond exactly to Lemma B.7; the fourth is its useful
strong-quasi-concavity companion.
