# Paper-facing declaration dependency index

This index presents the public declarations in the verified vertical proof
architecture. It connects the
manuscript's endpoint calculus, localization, necessity, sufficiency,
classification, and semiring/channel lift. The last column records the closest
project dependencies or the declaration's role; Mathlib calls are omitted.

This is a source-level dependency index, not a build certificate. In
particular, `ShannonLocalization.shannonLocalization` is the named integration
interface imported by the downstream Shannon arguments; its four outputs are
listed here because they are part of the final vertical API. Compilation and
forbidden-token audit results are reported separately.

The stable manuscript-facing names are defined in
[`ConditionalEntropy/FullDetailsStatements.lean`](../ConditionalEntropy/FullDetailsStatements.lean).
There is exactly one such facade for each numbered main-text environment
4.1--5.9. The authoritative number/label/name mapping, including the separate
Appendix A audit, is
[`full-details-correspondence.json`](full-details-correspondence.json). The
tables below list implementation dependencies and therefore remain
many-to-many by design.

## Endpoint-aware Rényi calculus and signed integration

| Lean declaration | Module | Direct project dependencies / manuscript role |
|---|---|---|
| `exactEntropyDerivativeFormulas` | `ConditionalEntropy.EndpointLineCalculus` | Packages the order-zero, Shannon, finite-order, and top-order first/second line derivatives. |
| `continuousWithinAt_entropyLine_top` | `ConditionalEntropy.EndpointParameterContinuity` | Extends the entropy line continuously to the top endpoint under a fixed maximizing coordinate. |
| `continuousOn_entropyLine_full_bundle` | `ConditionalEntropy.EndpointParameterContinuity` | Bundles continuity of the entropy line and both line derivatives on `Set.univ ×ˢ Icc (-lambda0) lambda0`. |
| `exactDerivatives` | `ConditionalEntropy.EndpointParameterContinuity` | Final endpoint-aware derivative/continuity package built on `exactEntropyDerivativeFormulas` and the top-endpoint continuation. |
| `signedLineColumnBridge` | `ConditionalEntropy.SignedLineCalculus` | Identifies the signed one-column witness with the integrated entropy line. |
| `signedLogPhiLineDerivativesOfIntegral` | `ConditionalEntropy.SignedLineCalculus` | Moves the first and second line derivatives through a signed parameter integral. |
| `uniformDCT` | `ConditionalEntropy.UniformSignedDCT` | Compact-uniform dominated convergence for a finite positive measure. |
| `uniformDCTSigned` | `ConditionalEntropy.UniformSignedDCT` | Signed-measure compact-uniform dominated convergence, used by block and Shannon limit passage. |

## Two-block and three-block localization

| Lean declaration | Module | Direct project dependencies / manuscript role |
|---|---|---|
| `blockLimitPassage` | `ConditionalEntropy.BlockLimitPassage` | Converts dominant-block pointwise estimates and domination into compact-uniform signed-integral convergence. |
| `twoBlockLimitIntegralEval` | `ConditionalEntropy.BlockLocalization` | Evaluates the exact two-block limit integral as the lower/upper truncation expression. |
| `threeBlockLimitIntegralEval` | `ConditionalEntropy.BlockLocalization` | Evaluates the exact three-block first/second limit integrals. |
| `blockCurveKernelBridge` | `ConditionalEntropy.BlockLocalizationInterfaces` | Supplies one common positive interval, differentiability, and equality of curve derivatives with block log kernels. |
| `blockGKernelIntegralBridge` | `ConditionalEntropy.BlockLocalizationInterfaces` | Identifies G-kernels with the signed integral formulation needed for limit passage. |
| `blockKernelRegularity` | `ConditionalEntropy.BlockLocalizationInterfaces` | Additivity, homogeneity, and continuity of block kernels. |
| `blockLogMassLimit` | `ConditionalEntropy.BlockLocalizationInterfaces` | Compact-uniform log-mass limit used in the exact localization statements. |
| `twoBlockLocalization` | `ConditionalEntropy.BlockLocalizationInterfaces` | Exact manuscript two-block localization, using `blockLimitPassage` and `twoBlockLimitIntegralEval`. |
| `threeBlockLocalization` | `ConditionalEntropy.BlockLocalizationInterfaces` | Exact manuscript three-block localization, using `blockLimitPassage` and `threeBlockLimitIntegralEval`. |
| `blockLocalization` | `ConditionalEntropy.BlockLocalizationInterfaces` | Conjunction of `twoBlockLocalization` and `threeBlockLocalization`. |
| `threeBlockGStationarityPackage` | `ConditionalEntropy.LocalizationStationarity` | Turns three-block G-kernel convergence and regularity into the stationarity package used by corrected quasiconvexity. |

## Shannon-point localization and corrected stationarity

| Lean declaration | Module | Direct project dependencies / manuscript role |
|---|---|---|
| `shannonKernelRegularity` | `ConditionalEntropy.ShannonKernelRegularityBridge` | Additivity/homogeneity of the first G-kernel and continuity of the first and second G-kernels. |
| `shannonCurveKernelBridge` | `ConditionalEntropy.ShannonCurveKernelBridge` | Common positive interval, `ContDiffOn` curve package, and equality of log/G curve derivatives with Shannon kernels. |
| `shannonLogMass` | `ConditionalEntropy.ShannonLogMass` | Compact-uniform vanishing of the first and second log-mass kernels, with the quantitative decay bound and exact negative-square identity. |
| `uniformShannonExpansion` | `ConditionalEntropy.ShannonExpansion` | Uniform `C²` rounded three-block expansion together with the exact order-one kernel limits. |
| `shannonNeighbourhood` | `ConditionalEntropy.ShannonExpansion` | Uniform near-order-one kernel bounds, fixed-order compact-uniform limits, and the two removable order-one limits. |
| `shannonLocalization` | `ConditionalEntropy.ShannonLocalization` | Four compact-uniform limits, in order: log q=1, log q=2, G q=1, and G q=2. |
| `shannonGStationarityPackage` | `ConditionalEntropy.NegativeTropicalShannonNecessity` | Converts the G parts of `shannonLocalization` into a `StationarityPackage`. |
| `shannonGCorrectedObstruction` | `ConditionalEntropy.NegativeTropicalShannonNecessity` | Applies corrected stationary-line obstruction to the Shannon G package and curve bridge. |
| `negativeTropicalUpperAtomZero` | `ConditionalEntropy.NegativeTropicalShannonNecessity` | Uses Shannon localization to rule out a nonzero atom at order one when upper support is nonempty. |

## Support, truncation, and moment passage

| Lean declaration | Module | Direct project dependencies / manuscript role |
|---|---|---|
| `negativeTruncationBridge` | `ConditionalEntropy.NecessityMeasureAlgebra` | Rewrites the negative signed witness in terms of lower and upper truncations. |
| `upperMoment_positiveSigned_neg_of_tail` | `ConditionalEntropy.NecessityMeasureAlgebra` | Identifies the signed upper-tail contribution needed by derivation necessity. |
| `MLower_le_of_null_truncated_lintegrals` | `ConditionalEntropy.NecessityMomentPassage` | Monotone-convergence passage from null thresholds to the lower moment. |
| `MLower_le_of_truncated_difference` | `ConditionalEntropy.NecessityMomentPassage` | Converts uniform truncated signed inequalities into a lower-moment bound. |
| `MUpper_lt_top_of_exceptional_support` | `ConditionalEntropy.NecessityExceptionalMeasureAlgebra` | Finiteness of the upper moment under a unique isolated upper support point. |
| `upperTrunc_eq_MUpper_toReal_of_exceptional_support` | `ConditionalEntropy.NecessityExceptionalMeasureAlgebra` | Exact upper-truncation evaluation below the isolated upper point. |
| `exceptionalUpperMeasurePackage` | `ConditionalEntropy.NecessityExceptionalMeasureAlgebra` | Bundles upper-moment finiteness, exact truncation, and positivity/isolation consequences. |

## Temperate necessity

| Lean declaration | Module | Direct project dependencies / manuscript role |
|---|---|---|
| `positiveUpperTailObstruction` | `ConditionalEntropy.PositiveTemperateNecessity` | Two-block concavity obstruction for support above one. |
| `positiveNecessitySupport` | `ConditionalEntropy.PositiveTemperateNecessity` | Uses the upper-tail obstruction to force support in `[0,1]`. |
| `positiveNecessityLowerMoment` | `ConditionalEntropy.PositiveTemperateNecessity` | Three-block localization and moment passage give `MLower ≤ 1`. |
| `positiveNecessity` | `ConditionalEntropy.PositiveNecessity` | Adds the Shannon atom-zero clause to support and lower-moment necessity. |
| `positiveTemperateProbabilityNecessity` | `ConditionalEntropy.PositiveNecessity` | Shape reduction plus finite-scale transport to the exact positive admissibility condition. |
| `twoUpperSupportPointsObstruction` | `ConditionalEntropy.NegativeTemperateNecessity` | Three-block convexity obstruction to two distinct support points above one. |
| `oneUpperPoint` | `ConditionalEntropy.NegativeTemperateNecessity` | Produces the lower-support-or-unique-upper-point dichotomy. |
| `truncatedMoment` | `ConditionalEntropy.NegativeTemperateNecessity` | Two-block localization yields the exceptional truncated moment inequality. |
| `negativeTemperateNecessity_of_atom_zero` | `ConditionalEntropy.NegativeTemperateNecessity` | Combines support isolation, exceptional upper algebra, and moment passage under the atom-zero hypothesis. |
| `negativeShannonObstruction` | `ConditionalEntropy.NegativeNecessity` | Shannon localization turns a nonzero order-one atom into the lower-support alternative. |
| `negativeTemperateNecessity` | `ConditionalEntropy.NegativeNecessity` | Complete lower-support-or-single-exceptional finite-measure conclusion. |
| `negativeTemperateProbabilityNecessity` | `ConditionalEntropy.NegativeNecessity` | Shape reduction and finite-scale transport to the exact negative admissibility disjunction. |

## Tropical and derivation necessity

| Lean declaration | Module | Direct project dependencies / manuscript role |
|---|---|---|
| `probAsPosConeIdentities` | `ConditionalEntropy.PositiveTropicalNecessity` | Cone identities for the probability interpolation used in the positive-tropical branch. |
| `sameSupportDecomposition` | `ConditionalEntropy.PositiveTropicalNecessity` | Decomposes same-support probability vectors into the interpolation geometry required by strong quasiconcavity. |
| `probabilityEqDiracZero` | `ConditionalEntropy.PositiveTropicalNecessity` | Measure argument identifying the only admissible parameter as `diracProb 0`. |
| `positiveTropicalNecessity` | `ConditionalEntropy.PositiveTropicalNecessity` | Transports conditional monotonicity through tropical shape reduction and concludes `tau = diracProb 0`. |
| `threeBlockGCorrectedObstruction` | `ConditionalEntropy.NegativeTropicalNecessity` | Applies `correctedStationaryLineObstruction` to `threeBlockGStationarityPackage`. |
| `twoUpperSupportPointsTropicalObstruction` | `ConditionalEntropy.NegativeTropicalNecessity` | Rules out two distinct upper support points from negative G quasiconvexity. |
| `oneUpperPointTropical` | `ConditionalEntropy.NegativeTropicalNecessity` | Tropical lower-support-or-unique-upper-point dichotomy. |
| `tropicalTruncatedMoment_of_exceptional` | `ConditionalEntropy.NegativeTropicalNecessity` | Corrected three-block stationarity gives the exceptional truncated tropical inequality. |
| `negativeTropicalNecessity_of_atom_zero` | `ConditionalEntropy.NegativeTropicalNecessity` | Support isolation plus monotone-convergence passage yields the finite-measure `NegTrop` conclusion. |
| `negGQuasiconvex_toFiniteMeasure_of_CMMonotone` | `ConditionalEntropy.NegativeTropicalNecessity` | Tropical shape reduction and `ULift` invariance produce the finite-measure quasiconvexity premise. |
| `negativeTropicalNecessity` | `ConditionalEntropy.NegativeTropicalNecessity` | Uses `negativeTropicalUpperAtomZero` and finite-measure transport for the final probability-parameter conclusion. |
| `derivationColumn_line_of_positive` | `ConditionalEntropy.DerivationNecessity` | Identifies the derivation column along a positive cone line. |
| `derivationBlockCurve_eq_mul` | `ConditionalEntropy.DerivationNecessity` | Rewrites the two-block derivation curve as the product used in the second-order obstruction. |
| `secondDeriv_mul_of_contDiffAt` | `ConditionalEntropy.DerivationNecessity` | Exact second-order product rule used at the stationary point. |
| `derivationNecessity` | `ConditionalEntropy.DerivationNecessity` | Two-block localization and upper-tail positivity force support in `[0,1]`. |

## Sufficiency and classification

| Lean declaration | Module | Direct project dependencies / manuscript role |
|---|---|---|
| `finiteSufficiency` | `ConditionalEntropy.FiniteSupportSufficiency` | Complete finite-support temperate sufficiency, including endpoint perturbations. |
| `generalSufficiency` | `ConditionalEntropy.GeneralSufficiency` | Discretization and curvature closure transport finite-support sufficiency to general measures. |
| `finiteTSufficiency` | `ConditionalEntropy.Section4Sufficiency` | Final nonzero finite-temperature sufficiency theorem. |
| `negativeTropicalSufficiency` | `ConditionalEntropy.Section4Sufficiency` | Final negative-tropical lower/exceptional sufficiency theorem. |
| `positiveTropicalSufficiency` | `ConditionalEntropy.Section4Sufficiency` | Final positive-tropical sufficiency theorem for `diracProb 0`. |
| `derivationSufficiency` | `ConditionalEntropy.Section4Sufficiency` | Final derivation sufficiency theorem for support in `[0,1]`. |
| `necessityBundle` | `ConditionalEntropy.NecessityBundle` | Combines `positiveTemperateProbabilityNecessity`, `negativeTemperateProbabilityNecessity`, `positiveTropicalNecessity`, `negativeTropicalNecessity`, and `derivationNecessity`. |
| `mainClassification` | `ConditionalEntropy.MainClassification` | Pairs `necessityBundle` with the four `Section4Sufficiency` conclusions to prove `Classifies`. |

## Original semiring/channel lift and candidate laws

| Lean declaration | Module | Direct project dependencies / manuscript role |
|---|---|---|
| `conditionalSemiringCommSemiring` | `ConditionalEntropy.FiniteSemiringQuotient` | The quotient of finite joint data by relabeling/zero-extension is a commutative semiring. |
| `CMRelCone.trans` | `ConditionalEntropy.FiniteChannelAlgebra` | Composition of cone-level conditional-majorization witnesses. |
| `CMRelCone.directSum` | `ConditionalEntropy.FiniteChannelAlgebra` | Compatibility of the relation with conditional direct sum. |
| `CMRelCone.tensor` | `ConditionalEntropy.FiniteChannelAlgebra` | Compatibility of the relation with tensor product. |
| `FixedRowCone.reflTransGen_cmRel_iff` | `ConditionalEntropy.FiniteChannelAlgebra` | Identifies the generated relation with concrete channel comparison at fixed row type. |
| `conditionalSemiringPreorder` | `ConditionalEntropy.ConditionalSemiringOrder` | Preorder on the conditional semiring induced by generated concrete channel comparisons. |
| `conditionalSemiring_le_iff_reflTransGen_concrete` | `ConditionalEntropy.ConditionalSemiringOrder` | Exact quotient-order characterization. |
| `conditionalSemiringOfJointProb_le` | `ConditionalEntropy.ConditionalSemiringOrder` | Lifts a concrete channel comparison between joint probabilities to the semiring order. |
| `semiringJointFunctional_embeddingInvariant` | `ConditionalEntropy.ConditionalSemiringOrder` | The joint functional induced by a semiring functional is embedding invariant. |
| `semiringJointFunctional_cmMonotone` | `ConditionalEntropy.ConditionalSemiringOrder` | Semiring-order monotonicity implies channel monotonicity of the induced joint functional. |
| `semiringJointFunctional_embeddingLift` | `ConditionalEntropy.ConditionalSemiringOrder` | Combines semiring-order monotonicity and the original embedding lift. |
| `embeddingLift` | `ConditionalEntropy.FiniteChannels` | Extends fixed-row conditional monotonicity plus embedding invariance to the embedded relation. |
| `candidateFairBitNormalization` | `ConditionalEntropy.CandidateNormalization` | Simultaneous fair-bit normalization for temperate, derivation, and both tropical candidates. |
| `candidateNonnegative` | `ConditionalEntropy.CandidateNormalization` | Simultaneous nonnegativity package for all four candidate families. |
| `candidateJointTensorAdditive` | `ConditionalEntropy.JointTensorCandidates` | Simultaneous tensor additivity package. |
| `candidateJointEmbeddingInvariant` | `ConditionalEntropy.CandidateEmbeddingInvariance` | Simultaneous joint zero-extension/embedding invariance package. |
| `allConditionalEntropyAxioms` | `ConditionalEntropy.AllConditionalEntropyAxioms` | Combines the four candidate packages, the four sufficiency branches, and `embeddingLift` into the literal five-part law bundle. |

The detailed Lean implementation dependency graph at module-group level is
[`dependency-graph.dot`](dependency-graph.dot). The manuscript statement table
remains in [`BLUEPRINT_STATEMENT_STATUS.md`](BLUEPRINT_STATEMENT_STATUS.md) and
its LaTeX counterpart.
