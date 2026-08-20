# Blueprint statement correspondence (Sections 4--5 and final assembly)

Scope: the 152 labeled `definition`, `lemma`, `proposition`, `corollary`, and
`theorem` environments beginning immediately after `sec:sufficiency` and
continuing through `cor:all-conditional-entropy-axioms`, in source order in
`paper/blueprint-sections-4-5.tex`. `Proved and kernel checked` means that the
listed Lean declaration proves the row's full blueprint conclusion. `Partial
algebraic kernel` means that it checks a genuine finite algebraic or
order-theoretic component but not the full statement. An em dash means that no
existing project declaration is a semantically justified correspondence. In
particular, the necessity bundle, complete classification, and complete axiom
bundle are not claimed as checked.

| Manuscript statement | Lean declaration | Status |
|---|---|---|
| `lem:origin-extension` — Extension from the punctured cone | `ConditionalEntropy.originExtension` | Proved and kernel checked |
| `lem:punctured-cone-convex` — Convexity of the punctured nonnegative cone | `ConditionalEntropy.puncturedConeConvex` | Proved and kernel checked |
| `lem:composition-rule` — Monotone composition rule | `ConditionalEntropy.compositionRule` | Proved and kernel checked |
| `lem:cone-composition-rule` — Monotone composition on the punctured cone | `ConditionalEntropy.coneCompositionRule` | Proved and kernel checked |
| `lem:finite-holder` — Finite Hölder inequality | — | Not formalized |
| `lem:power-curvature` — Power-mean curvature | — | Not formalized |
| `lem:parameter-power-curvature` — Compactified power-mean bridge | — | Not formalized |
| `def:hessian-quad` — Hessian quadratic form | — | Not formalized |
| `lem:hessian-sign-criterion` — Hessian sign criterion | — | Not formalized |
| `lem:real-rpow-calculus` — Positive-base real-power calculus | — | Not formalized |
| `lem:monomial-curvature` — Curvature of an affine monomial | `ConditionalEntropy.monomialCurvature`;<br>`ConditionalEntropy.monomialCurvature_eq_neg_variance`;<br>`ConditionalEntropy.monomialCurvature_nonpos_of_nonneg`;<br>`ConditionalEntropy.coefficient_mem_Icc_of_curvature_nonpos`;<br>`ConditionalEntropy.monomialCurvature_pos_of_negative_coefficient`;<br>`ConditionalEntropy.two_positive_stationary_witness`;<br>`ConditionalEntropy.negativeTemperate_two_coefficient_curvature` | Partial algebraic kernel |
| `lem:finite-support-enumeration` — Enumeration of a finite probability support | — | Not formalized |
| `lem:finite-support-dirac` — Finite-support measure decomposition | — | Not formalized |
| `prop:finite-sufficiency` — Finite-support sufficiency | `ConditionalEntropy.positiveTemperate_coefficients_nonnegative`;<br>`ConditionalEntropy.negativeTemperate_two_coefficient_curvature` | Partial algebraic kernel |
| `prop:general-sufficiency` — General temperate sufficiency | `ConditionalEntropy.isConcave_of_pointwise_tendsto`;<br>`ConditionalEntropy.isConvex_of_pointwise_tendsto`;<br>`ConditionalEntropy.conditioning_monotone_of_concave`;<br>`ConditionalEntropy.conditioning_antitone_of_convex` | Partial algebraic kernel |
| `cor:finite-t-sufficiency` — Finite-$t$ sufficiency | `ConditionalEntropy.positiveTemperate_coefficients_nonnegative`;<br>`ConditionalEntropy.negativeTemperate_two_coefficient_curvature`;<br>`ConditionalEntropy.conditioning_monotone_of_concave`;<br>`ConditionalEntropy.conditioning_antitone_of_convex` | Partial algebraic kernel |
| `prop:negative-tropical-sufficiency` — Negative tropical sufficiency | `ConditionalEntropy.isQuasiConvex_of_pointwise_tendsto` | Partial algebraic kernel |
| `lem:positive-tropical-component` — Positive tropical component formula | — | Not formalized |
| `prop:positive-tropical-sufficiency` — Positive tropical sufficiency | `ConditionalEntropy.isStronglyQuasiConcave_of_pointwise_tendsto` | Partial algebraic kernel |
| `def:derivation-family` — Derivation polymorphic family | — | Not formalized |
| `prop:derivation-sufficiency` — Derivation sufficiency | — | Not formalized |
| `def:signed-column-functions` — Signed-measure column functions | — | Not formalized |
| `def:signed-witness-predicates` — Positive and negative signed witnesses | — | Not formalized |
| `lem:signed-witness-bridge` — Scaling, total variation, support, and atoms of witnesses | — | Not formalized |
| `lem:signed-scalar-column-bridge` — Signed-scalar bridge to the candidate column functions | — | Not formalized |
| `def:finite-param` — Embedding a finite real order | — | Not formalized |
| `def:positive-line-data` — Positive multiplicative line data | — | Not formalized |
| `def:positive-line-raw` — Raw multiplicative line | — | Not formalized |
| `def:positive-line-predicate` — Positivity predicate for a line | — | Not formalized |
| `lem:line-positive-zero` — The base point of a positive line is positive | — | Not formalized |
| `def:line-cone` — Proof-carrying cone versions of a positive line | — | Not formalized |
| `def:positive-line-prob` — Total normalized line | — | Not formalized |
| `def:scalar-qcvx-on` — Scalar quasiconvexity on a set | `ConditionalEntropy.IsQuasiConvex` | Partial algebraic kernel |
| `lem:cone-affine-line-bridge` — Restricting cone curvature to a positive affine line | — | Not formalized |
| `def:entropy-line` — Entropy line | — | Not formalized |
| `def:entropy-line-first` — First entropy line derivative | — | Not formalized |
| `def:entropy-line-second` — Second entropy line derivative | — | Not formalized |
| `def:escort-weight` — Escort weight | — | Not formalized |
| `def:effective-line-velocity` — Effective line velocity | — | Not formalized |
| `def:escort-mean` — Escort mean | `ConditionalEntropy.weightedMean` | Partial algebraic kernel |
| `def:escort-second` — Escort second moment | `ConditionalEntropy.weightedSecondMoment` | Partial algebraic kernel |
| `def:escort-variance` — Escort variance | `ConditionalEntropy.weightedVariance` | Partial algebraic kernel |
| `def:fixed-max-coordinate` — Fixed maximal-coordinate condition | — | Not formalized |
| `lem:positivity-intervals` — Common positivity and maximal-coordinate intervals | — | Not formalized |
| `def:iterated-deriv` — Iterated one-variable derivative | — | Not formalized |
| `def:lambda-deriv` — Iterated derivative in the second variable | — | Not formalized |
| `def:alpha-lambda-deriv` — Mixed parameter--line derivative | — | Not formalized |
| `def:removable-shannon-quotient` — Removable Shannon quotient | — | Not formalized |
| `lem:parameterized-removable-quotient` — Parameterized removable quotient at the Shannon point | — | Not formalized |
| `lem:signed-integral-differentiate-twice` — Twice differentiating a finite signed-measure integral | — | Not formalized |
| `def:shannon-line-slope` — Shannon line slope | — | Not formalized |
| `lem:exact-derivatives` — Exact entropy derivatives | — | Not formalized |
| `def:integrated-entropy-line` — Integrated entropy along a line | — | Not formalized |
| `def:signed-log-phi-line` — Signed logarithmic column line | — | Not formalized |
| `lem:signed-line-column-bridge` — Exact bridge from line kernels to signed column functions | — | Not formalized |
| `lem:differentiate-integral` — Differentiation through the parameter integral | — | Not formalized |
| `lem:null-thresholds` — Null thresholds | — | Not formalized |
| `lem:two-upper-null-thresholds` — Two finite null thresholds between upper parameters | — | Not formalized |
| `lem:support-strict-integral` — Support gives strict weighted mass | — | Not formalized |
| `lem:scalar-measure-support` — Scalar measure support and null points | — | Not formalized |
| `def:block-index` — Finite dependent block carrier | — | Not formalized |
| `def:block-vector` — Constant-on-block vector | — | Not formalized |
| `def:block-data` — Asymptotic block data | — | Not formalized |
| `lem:block-count-pos` — Positive block counts | — | Not formalized |
| `def:block-carrier-nonempty` — Nonempty block-carrier instance | — | Not formalized |
| `def:block-index-nonempty` — Nonempty arbitrary block index | — | Not formalized |
| `def:block-max` — Maximum of a nonempty block vector | — | Not formalized |
| `def:block-line-data` — Typed block line | — | Not formalized |
| `def:block-kernels` — Block exponents, escort weights, and derivative kernels | — | Not formalized |
| `lem:block-vector-formulas` — Block-vector finite-sum formulas | — | Not formalized |
| `lem:rounding` — Rounding estimates | — | Not formalized |
| `lem:dominant-block` — Dominant-block escort estimate | `ConditionalEntropy.dominantBlock_first`;<br>`ConditionalEntropy.dominantBlock_second` | Partial algebraic kernel |
| `lem:near-shannon-dominant` — Near-Shannon cancellation for a dominant block | — | Not formalized |
| `lem:large-alpha-tail` — Large-order tail bound | — | Not formalized |
| `def:block-limit-kernels` — Pointwise limit kernels for a block family | — | Not formalized |
| `prop:block-limit-passage` — Uniform passage to the block limit | — | Not formalized |
| `def:special-block-data` — Specialized block data and signed truncations | — | Not formalized |
| `def:special-block-top-unique` — Unique top blocks for the special families | — | Not formalized |
| `def:block-dominance-maps` — Total two-block and three-block dominance maps | — | Not formalized |
| `lem:two-block-dominance-package` — Exact two-block dominance package | — | Not formalized |
| `lem:three-block-dominance-package` — Exact three-block dominance package | — | Not formalized |
| `lem:two-order-one-dominance` — Unique order-one block for the two-block family | — | Not formalized |
| `lem:three-order-one-dominance` — Unique order-one block for the three-block family | — | Not formalized |
| `def:block-log-g-kernels` — Block logarithmic and norm-free kernels | — | Not formalized |
| `lem:compact-uniform-eval` — Evaluation of compact-uniform convergence | — | Not formalized |
| `lem:compact-uniform-add` — Addition closure for compact-uniform convergence | — | Not formalized |
| `lem:compact-uniform-singleton` — Evaluation on a singleton | — | Not formalized |
| `lem:subtype-uniform-error-bridge` — Subtype bridge for uniform signed-integral errors | — | Not formalized |
| `lem:block-curve-kernel-bridge` — Block curve--kernel bridge | — | Not formalized |
| `lem:block-g-kernel-integrals` — Block (G)-kernels are signed kernel integrals | — | Not formalized |
| `lem:block-log-mass-limit` — Block logarithmic-mass splitting and limit | — | Not formalized |
| `lem:block-log-mass-continuity` — Continuity of logarithmic block-mass kernels | — | Not formalized |
| `lem:block-kernel-regularity` — Linearity and continuity of the block kernels | — | Not formalized |
| `def:two-block-limits` — Two-block limit polynomials | — | Not formalized |
| `def:three-block-limits` — Three-block cells and limit polynomials | — | Not formalized |
| `lem:two-block-limit-integral-eval` — Evaluation of the two-block limit integrals | — | Not formalized |
| `lem:three-block-limit-integral-eval` — Evaluation of the three-block limit integrals | — | Not formalized |
| `prop:block-localisation` — Two-block and three-block localisation | — | Not formalized |
| `prop:two-block-localisation` — Two-block localisation interface | — | Not formalized |
| `prop:three-block-localisation` — Three-block localisation interface | — | Not formalized |
| `def:shannon-data` — Shannon block data | — | Not formalized |
| `lem:shannon-q-pos` — Positivity of the complementary Shannon weight | — | Not formalized |
| `lem:shannon-log-scale-pos` — Positivity of the Shannon logarithmic scale | — | Not formalized |
| `lem:shannon-count-pos` — Positive Shannon block counts | — | Not formalized |
| `def:shannon-index-nonempty` — Nonempty Shannon index and block representative | — | Not formalized |
| `def:shannon-line-data` — Shannon line and its escort | — | Not formalized |
| `lem:shannon-top-unique-at-zero` — The third Shannon block is strictly maximal at the base point | — | Not formalized |
| `def:shannon-kernels` — Named Shannon kernels | — | Not formalized |
| `lem:shannon-curve-kernel-bridge` — Shannon curve--kernel bridge | — | Not formalized |
| `lem:shannon-kernel-integral-bridge` — Shannon derivative--integral and logarithmic splitting bridge | — | Not formalized |
| `lem:shannon-kernel-regularity` — Linearity and continuity of the Shannon kernels | — | Not formalized |
| `lem:shannon-dedicated-escort` — Dedicated Shannon escort, compact-region, and tail estimates | — | Not formalized |
| `def:shannon-remainder` — Shannon main term and uniform remainder | — | Not formalized |
| `lem:uniform-shannon-expansion` — Uniform Shannon expansion | — | Not formalized |
| `lem:shannon-neighbourhood` — Uniform control near the Shannon point | — | Not formalized |
| `def:remove-signed-atom` — Signed atom and its removal | — | Not formalized |
| `lem:remove-signed-atom` — Removing a signed atom | — | Not formalized |
| `lem:signed-witness-integral-bridge` — Witness atoms and the positive lower truncation | — | Not formalized |
| `lem:shannon-log-mass` — Shannon-block logarithmic mass derivatives | — | Not formalized |
| `def:shannon-localization-targets` — Shannon localization targets | — | Not formalized |
| `prop:shannon-localisation` — Shannon-point localisation | — | Not formalized |
| `def:normalized-curvature` — Normalized scalar-line curvature | — | Not formalized |
| `lem:log-curvature-identity` — Logarithmic curvature identity | — | Not formalized |
| `lem:log-curvature-obstruction` — Logarithmic curvature limit obstruction | — | Not formalized |
| `def:stationarity-package` — Stationarity convergence package | — | Not formalized |
| `lem:stationarity-correction` — Exact stationarity correction | `ConditionalEntropy.stationarityCorrection_dot`;<br>`ConditionalEntropy.stationarityCorrection_tendsto` | Partial algebraic kernel |
| `lem:quasiconvex-second` — Stationary curvature of a quasi-convex function | `ConditionalEntropy.not_quasiConvex_of_strict_midpoint_peak` | Partial algebraic kernel |
| `lem:typed-log-curvature-contradiction` — Typed curvature contradiction from logarithmic kernels | `ConditionalEntropy.not_concave_of_strict_midpoint_valley`;<br>`ConditionalEntropy.not_convex_of_strict_midpoint_peak` | Partial algebraic kernel |
| `lem:corrected-stationary-line-obstruction` — Corrected stationary-line obstruction | `ConditionalEntropy.stationarityCorrection_dot`;<br>`ConditionalEntropy.stationarityCorrection_tendsto`;<br>`ConditionalEntropy.not_quasiConvex_of_strict_midpoint_peak` | Partial algebraic kernel |
| `prop:positive-necessity` — Positive-measure obstruction | `ConditionalEntropy.negative_tail_concavity_obstruction`;<br>`ConditionalEntropy.excessive_lower_moment_concavity_obstruction`;<br>`ConditionalEntropy.shannon_atom_concavity_obstruction`;<br>`ConditionalEntropy.positiveTemperate_shannon_atom_zero`;<br>`ConditionalEntropy.positiveTemperate_no_upper_moment`;<br>`ConditionalEntropy.positiveTemperate_lowerMoment_le_one`;<br>`ConditionalEntropy.positiveTemperate_necessary` | Partial algebraic kernel |
| `cor:positive-temperate-probability-necessity` — Positive temperate necessity for probability measures | `ConditionalEntropy.positiveTemperate_necessary` | Partial algebraic kernel |
| `prop:negative-shannon-obstruction` — A Shannon atom excludes upper support | — | Not formalized |
| `def:negative-truncations` — Positive lower and upper truncations | — | Not formalized |
| `lem:negative-truncation-bridge` — Negative-witness truncation identities | — | Not formalized |
| `prop:truncated-moment` — Truncated-moment obstruction | `ConditionalEntropy.two_positive_stationary_witness`;<br>`ConditionalEntropy.negativeTemperate_truncated_moment`;<br>`ConditionalEntropy.negativeTemperate_exceptional_moment` | Partial algebraic kernel |
| `prop:one-upper-point` — At most one upper support point | `ConditionalEntropy.two_positive_stationary_witness`;<br>`ConditionalEntropy.negativeTemperate_atMostOneUpperCell` | Partial algebraic kernel |
| `prop:negative-temperate-necessity` — Complete negative temperate necessity | `ConditionalEntropy.negativeTemperate_exceptional_moment`;<br>`ConditionalEntropy.negativeTemperate_atMostOneUpperCell` | Partial algebraic kernel |
| `cor:negative-temperate-probability-necessity` — Negative temperate necessity for probability measures | `ConditionalEntropy.negativeTemperate_exceptional_moment`;<br>`ConditionalEntropy.negativeTemperate_atMostOneUpperCell` | Partial algebraic kernel |
| `prop:negative-tropical-necessity` — Complete negative tropical necessity | `ConditionalEntropy.negativeTropical_moment_nonnegative`;<br>`ConditionalEntropy.negativeTropical_exceptional_moment` | Partial algebraic kernel |
| `def:prob-as-pos-cone` — Probability support as a positive cone vector | — | Not formalized |
| `lem:prob-as-pos-cone-identities` — Probability-to-cone identities | — | Not formalized |
| `lem:prob-support-nonempty` — A probability vector has nonempty positive support | — | Not formalized |
| `lem:same-support-decomposition` — Decomposition inside a simplex face | — | Not formalized |
| `lem:probability-eq-dirac-zero` — Probability supported at zero is the zero Dirac measure | — | Not formalized |
| `prop:positive-tropical-necessity` — Only the support-rank measure survives | — | Not formalized |
| `def:derivation-column-function` — Derivation column function | — | Not formalized |
| `prop:derivation-necessity` — Derivation necessity | `ConditionalEntropy.positive_tail_derivation_obstruction`;<br>`ConditionalEntropy.derivation_no_positive_upper_tail`;<br>`ConditionalEntropy.derivation_necessary` | Partial algebraic kernel |
| `thm:necessity-bundle` — All necessary parameter conditions | `ConditionalEntropy.positiveTemperate_necessary`;<br>`ConditionalEntropy.negativeTemperate_exceptional_moment`;<br>`ConditionalEntropy.negativeTropical_exceptional_moment`;<br>`ConditionalEntropy.derivation_necessary` | Partial algebraic kernel |
| `thm:main-classification` — Complete parameter classification | — | Not formalized |
| `def:conditional-entropy-axioms` — Conditional-entropy axiom bundle | — | Not formalized |
| `lem:embedding-lift` — Embedding lift of fixed-row monotonicity | — | Not formalized |
| `cor:all-conditional-entropy-axioms` — Admissible candidates satisfy the complete axiom bundle | — | Not formalized |
