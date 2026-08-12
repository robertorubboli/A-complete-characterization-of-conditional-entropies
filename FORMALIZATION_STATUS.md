# Formalization status

The project builds with Lean 4.32.2 and Mathlib 4.32.2. It is a
kernel-checked formalization of the finite coefficient and order-theoretic
core of the replacement Sections 4 and 5, organized so that analytic boundary
facts live in standalone modules and paper-facing conclusions import their
proofs.

## Unconditional checked declarations

The following results have no project-specific assumptions beyond the
mathematical hypotheses displayed in their statements:

- `conditioning_monotone_of_concave` and
  `conditioning_antitone_of_convex`: the Appendix A implication from
  one-column shape and positive homogeneity to monotonicity under arbitrary
  finite row-stochastic conditioning maps;
- `monomialCurvature_eq_neg_variance` and
  `monomialCurvature_nonpos_of_nonneg`: the affine-monomial Hessian/variance
  calculation used in Lemma 4.2;
- `coefficient_mem_Icc_of_curvature_nonpos`: necessity of nonnegative affine
  coefficients for concavity;
- `two_positive_stationary_witness`: the explicit stationary negative-curvature
  direction used in Propositions 5.3 and 5.6;
- `stationarityCorrection_dot` and `stationarityCorrection_tendsto`: Lemma B.15;
- the three `not_*_of_strict_midpoint_*` declarations: the finite endpoint
  arguments of Appendix B.6;
- `positiveTemperate_necessary`,
  `negativeTemperate_exceptional_moment`,
  `negativeTropical_exceptional_moment`, and `derivation_necessary`: the
  assembled finite-profile parameter consequences.

## Explicit abstraction boundary

The present version does **not** yet claim a complete formalization of every
measure-theoretic and asymptotic line of the 33-page replacement draft. In
particular, the following remain future work:

- a native Lean definition of the full Rényi-parameter integral on
  `[0,+∞]` and its endpoint values;
- Lemma 4.1 for all finite nonnegative vectors and every real power parameter;
- the general-measure discretization and dominated-convergence argument of
  Proposition 4.4 and Appendix B.1;
- Schur concavity of all Rényi endpoint entropies and the extension from
  conditioning maps to all conditionally mixing channels;
- the differentiated Rényi formulas and derivative-integral interchange of
  Appendix B.2; and
- the full two-block, three-block, and Shannon-point localization limits of
  Appendices B.3--B.4.

Accordingly, the finite coefficient profiles in
`ConditionalEntropy/ParameterConditions.lean` abstract the moments and support
data produced by those analytic arguments. The repository does not hide this
boundary behind an axiom: the paper-facing theorems expose every needed
curvature hypothesis explicitly, and the proved algebraic deductions are
unconditional once those hypotheses are supplied.

## Axiom policy

There are no declarations introduced with `axiom`, and no proof contains
`sorry` or `admit`. The automated audit builds with warnings as errors, scans
the project source for these tokens, and uses `#print axioms` on the main and
boundary declarations. The expected kernel dependencies are Lean's standard
logical infrastructure, such as `propext`, `Classical.choice`, and
`Quot.sound`.
