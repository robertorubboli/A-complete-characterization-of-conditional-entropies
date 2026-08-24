# Blueprint statement correspondence (Sections 4--5 and final assembly)

Scope: the 152 labeled manuscript statements from `lem:origin-extension` through
`cor:all-conditional-entropy-axioms`, in exact source order. “Formalized” means a
matching Lean declaration is present and covered by the strict root build;
“Formalized (split API)” means the manuscript package is represented by the listed
declarations, all of which are covered by that build.

| Manuscript statement | Lean declaration | Status |
|---|---|---|
| `lem:origin-extension` — Extension from the punctured cone | `ConditionalEntropy.originExtension` | Formalized |
| `lem:punctured-cone-convex` — Convexity of the punctured nonnegative cone | `ConditionalEntropy.puncturedConeConvex` | Formalized |
| `lem:composition-rule` — Monotone composition rule | `ConditionalEntropy.compositionRule` | Formalized |
| `lem:cone-composition-rule` — Monotone composition on the punctured cone | `ConditionalEntropy.coneCompositionRule` | Formalized |
| `lem:finite-holder` — Finite Hölder inequality | `ConditionalEntropy.finiteHolder` | Formalized |
| `lem:power-curvature` — Power-mean curvature | `ConditionalEntropy.powerCurvature` | Formalized |
| `lem:parameter-power-curvature` — Compactified power-mean bridge | `ConditionalEntropy.parameterPowerCurvature` | Formalized |
| `def:hessian-quad` — Hessian quadratic form | `ConditionalEntropy.hessianQuad` | Formalized |
| `lem:hessian-sign-criterion` — Hessian sign criterion | `ConditionalEntropy.hessianSignCriterion` | Formalized |
| `lem:real-rpow-calculus` — Positive-base real-power calculus | `ConditionalEntropy.realRpowCalculus` | Formalized |
| `lem:monomial-curvature` — Curvature of an affine monomial | `ConditionalEntropy.affineMonomialCurvaturePackage` | Formalized |
| `lem:finite-support-enumeration` — Enumeration of a finite probability support | `ConditionalEntropy.finiteSupportEnumeration` | Formalized |
| `lem:finite-support-dirac` — Finite-support measure decomposition | `ConditionalEntropy.finiteSupportDirac` | Formalized |
| `prop:finite-sufficiency` — Finite-support sufficiency | `ConditionalEntropy.finiteSufficiency` | Formalized |
| `prop:general-sufficiency` — General temperate sufficiency | `ConditionalEntropy.generalSufficiency` | Formalized |
| `cor:finite-t-sufficiency` — Finite-$t$ sufficiency | `ConditionalEntropy.finiteTSufficiency` | Formalized |
| `prop:negative-tropical-sufficiency` — Negative tropical sufficiency | `ConditionalEntropy.negativeTropicalSufficiency` | Formalized |
| `lem:positive-tropical-component` — Positive tropical component formula | `ConditionalEntropy.positiveTropicalComponent` | Formalized |
| `prop:positive-tropical-sufficiency` — Positive tropical sufficiency | `ConditionalEntropy.positiveTropicalSufficiency` | Formalized |
| `def:derivation-family` — Derivation polymorphic family | `ConditionalEntropy.derivationFamily` | Formalized |
| `prop:derivation-sufficiency` — Derivation sufficiency | `ConditionalEntropy.derivationSufficiency` | Formalized |
| `def:signed-column-functions` — Signed-measure column functions | `ConditionalEntropy.integratedEntropySigned`; `ConditionalEntropy.PhiSigned`; `ConditionalEntropy.GSigned` | Formalized (split API) |
| `def:signed-witness-predicates` — Positive and negative signed witnesses | `ConditionalEntropy.positiveSigned`; `ConditionalEntropy.negativeSigned`; `ConditionalEntropy.PosPhiConcave`; `ConditionalEntropy.NegPhiConvex`; `ConditionalEntropy.NegGQuasiconvex` | Formalized (split API) |
| `lem:signed-witness-bridge` — Scaling, total variation, support, and atoms of witnesses | `ConditionalEntropy.signedWitnessBridge` | Formalized |
| `lem:signed-scalar-column-bridge` — Signed-scalar bridge to the candidate column functions | `ConditionalEntropy.signedScalarColumnBridge` | Formalized |
| `def:finite-param` — Embedding a finite real order | `ConditionalEntropy.finiteParam` | Formalized |
| `def:positive-line-data` — Positive multiplicative line data | `ConditionalEntropy.PositiveLineData` | Formalized |
| `def:positive-line-raw` — Raw multiplicative line | `ConditionalEntropy.lineRaw` | Formalized |
| `def:positive-line-predicate` — Positivity predicate for a line | `ConditionalEntropy.LinePositive` | Formalized |
| `lem:line-positive-zero` — The base point of a positive line is positive | `ConditionalEntropy.linePositiveZero` | Formalized |
| `def:line-cone` — Proof-carrying cone versions of a positive line | `ConditionalEntropy.lineCone`; `ConditionalEntropy.linePosCone`; `ConditionalEntropy.lineConeTotal`; `ConditionalEntropy.linePosConeTotal` | Formalized (split API) |
| `def:positive-line-prob` — Total normalized line | `ConditionalEntropy.lineProb` | Formalized |
| `def:scalar-qcvx-on` — Scalar quasiconvexity on a set | `ConditionalEntropy.ScalarQCvxOn` | Formalized |
| `lem:cone-affine-line-bridge` — Restricting cone curvature to a positive affine line | `ConditionalEntropy.coneAffineLineBridge` | Formalized |
| `def:entropy-line` — Entropy line | `ConditionalEntropy.entropyLine` | Formalized |
| `def:entropy-line-first` — First entropy line derivative | `ConditionalEntropy.entropyLineFirst` | Formalized |
| `def:entropy-line-second` — Second entropy line derivative | `ConditionalEntropy.entropyLineSecond` | Formalized |
| `def:escort-weight` — Escort weight | `ConditionalEntropy.escortWeight` | Formalized |
| `def:effective-line-velocity` — Effective line velocity | `ConditionalEntropy.effectiveVelocity` | Formalized |
| `def:escort-mean` — Escort mean | `ConditionalEntropy.escortMean` | Formalized |
| `def:escort-second` — Escort second moment | `ConditionalEntropy.escortSecond` | Formalized |
| `def:escort-variance` — Escort variance | `ConditionalEntropy.escortVar` | Formalized |
| `def:fixed-max-coordinate` — Fixed maximal-coordinate condition | `ConditionalEntropy.FixedMaxCoordinate` | Formalized |
| `lem:positivity-intervals` — Common positivity and maximal-coordinate intervals | `ConditionalEntropy.exists_uniform_coordinate_bound`; `ConditionalEntropy.exists_uniform_shannonVelocity_bound`; `ConditionalEntropy.exists_fixedMaxCoordinate_blockLine`; `ConditionalEntropy.exists_fixedMaxCoordinate_shannonLine` | Formalized (split API) |
| `def:iterated-deriv` — Iterated one-variable derivative | `ConditionalEntropy.iteratedDeriv` | Formalized |
| `def:lambda-deriv` — Iterated derivative in the second variable | `ConditionalEntropy.lambdaDeriv` | Formalized |
| `def:alpha-lambda-deriv` — Mixed parameter--line derivative | `ConditionalEntropy.alphaLambdaDeriv` | Formalized |
| `def:removable-shannon-quotient` — Removable Shannon quotient | `ConditionalEntropy.removableShannonQuotient` | Formalized |
| `lem:parameterized-removable-quotient` — Parameterized removable quotient at the Shannon point | `ConditionalEntropy.parameterizedRemovableShannonQuotient` | Formalized |
| `lem:signed-integral-differentiate-twice` — Twice differentiating a finite signed-measure integral | `ConditionalEntropy.signedIntegral_differentiate_twice` | Formalized |
| `def:shannon-line-slope` — Shannon line slope | `ConditionalEntropy.shannonLineSlope` | Formalized |
| `lem:exact-derivatives` — Exact entropy derivatives | `ConditionalEntropy.exactDerivatives` | Formalized |
| `def:integrated-entropy-line` — Integrated entropy along a line | `ConditionalEntropy.integratedEntropyLine` | Formalized |
| `def:signed-log-phi-line` — Signed logarithmic column line | `ConditionalEntropy.signedLogPhiLine` | Formalized |
| `lem:signed-line-column-bridge` — Exact bridge from line kernels to signed column functions | `ConditionalEntropy.signedLineColumnBridge` | Formalized |
| `lem:differentiate-integral` — Differentiation through the parameter integral | `ConditionalEntropy.signedIntegral_differentiate_twice`; `ConditionalEntropy.signedLogPhiLineDerivativesOfIntegral` | Formalized (split API) |
| `lem:null-thresholds` — Null thresholds | `ConditionalEntropy.nullThresholds` | Formalized |
| `lem:two-upper-null-thresholds` — Two finite null thresholds between upper parameters | `ConditionalEntropy.twoUpperNullThresholds` | Formalized |
| `lem:support-strict-integral` — Support gives strict weighted mass | `ConditionalEntropy.supportStrictIntegral` | Formalized |
| `lem:scalar-measure-support` — Scalar measure support and null points | `ConditionalEntropy.scalarMeasureSupport` | Formalized |
| `def:block-index` — Finite dependent block carrier | `ConditionalEntropy.BlockIndex` | Formalized |
| `def:block-vector` — Constant-on-block vector | `ConditionalEntropy.blockVec` | Formalized |
| `def:block-data` — Asymptotic block data | `ConditionalEntropy.BlockData` | Formalized |
| `lem:block-count-pos` — Positive block counts | `ConditionalEntropy.blockCount_pos` | Formalized |
| `def:block-carrier-nonempty` — Nonempty block-carrier instance | `ConditionalEntropy.blockCarrierNonempty` | Formalized |
| `def:block-index-nonempty` — Nonempty arbitrary block index | `ConditionalEntropy.blockIndexNonempty` | Formalized |
| `def:block-max` — Maximum of a nonempty block vector | `ConditionalEntropy.blockMax` | Formalized |
| `def:block-line-data` — Typed block line | `ConditionalEntropy.blockBase`; `ConditionalEntropy.blockVelocity`; `ConditionalEntropy.blockLineData`; `ConditionalEntropy.blockLineRaw` | Formalized (split API) |
| `def:block-kernels` — Block exponents, escort weights, and derivative kernels | `ConditionalEntropy.blockExponent`; `ConditionalEntropy.blockContribution`; `ConditionalEntropy.blockEscort`; `ConditionalEntropy.blockEscortMean`; `ConditionalEntropy.blockEscortSecond`; `ConditionalEntropy.blockEscortVar`; `ConditionalEntropy.blockKernelFirst`; `ConditionalEntropy.blockKernelSecond` | Formalized (split API) |
| `lem:block-vector-formulas` — Block-vector finite-sum formulas | `ConditionalEntropy.blockVectorFormulas` | Formalized |
| `lem:rounding` — Rounding estimates | `ConditionalEntropy.roundingEstimates` | Formalized |
| `lem:dominant-block` — Dominant-block escort estimate | `ConditionalEntropy.dominantBlock` | Formalized |
| `lem:near-shannon-dominant` — Near-Shannon cancellation for a dominant block | `ConditionalEntropy.nearShannonDominant` | Formalized |
| `lem:large-alpha-tail` — Large-order tail bound | `ConditionalEntropy.largeAlphaTail` | Formalized |
| `def:block-limit-kernels` — Pointwise limit kernels for a block family | `ConditionalEntropy.blockLimitFirst`; `ConditionalEntropy.blockLimitSecond` | Formalized (split API) |
| `prop:block-limit-passage` — Uniform passage to the block limit | `ConditionalEntropy.blockLimitPassage` | Formalized |
| `def:special-block-data` — Specialized block data and signed truncations | `ConditionalEntropy.twoBlockData`; `ConditionalEntropy.threeBlockData`; `ConditionalEntropy.lowerMoment`; `ConditionalEntropy.upperMoment` | Formalized (split API) |
| `def:special-block-top-unique` — Unique top blocks for the special families | `ConditionalEntropy.twoBlockTopUnique`; `ConditionalEntropy.threeBlockTopUnique` | Formalized (split API) |
| `def:block-dominance-maps` — Total two-block and three-block dominance maps | `ConditionalEntropy.twoDominanceMap`; `ConditionalEntropy.threeDominanceMap` | Formalized (split API) |
| `lem:two-block-dominance-package` — Exact two-block dominance package | `ConditionalEntropy.twoBlockDominancePackage` | Formalized |
| `lem:three-block-dominance-package` — Exact three-block dominance package | `ConditionalEntropy.threeBlockDominancePackage` | Formalized |
| `lem:two-order-one-dominance` — Unique order-one block for the two-block family | `ConditionalEntropy.twoOrderOneDominancePackage` | Formalized |
| `lem:three-order-one-dominance` — Unique order-one block for the three-block family | `ConditionalEntropy.threeOrderOneDominant` | Formalized |
| `def:block-log-g-kernels` — Block logarithmic and norm-free kernels | `ConditionalEntropy.blockLogKernel`; `ConditionalEntropy.blockGKernel` | Formalized (split API) |
| `lem:compact-uniform-eval` — Evaluation of compact-uniform convergence | `ConditionalEntropy.compactUniformEval` | Formalized |
| `lem:compact-uniform-add` — Addition closure for compact-uniform convergence | `ConditionalEntropy.compactUniformConverges_add` | Formalized |
| `lem:compact-uniform-singleton` — Evaluation on a singleton | `ConditionalEntropy.compactUniformSingleton` | Formalized |
| `lem:subtype-uniform-error-bridge` — Subtype bridge for uniform signed-integral errors | `ConditionalEntropy.subtypeUniformErrorBridge` | Formalized |
| `lem:block-curve-kernel-bridge` — Block curve--kernel bridge | `ConditionalEntropy.blockCurveKernelBridge` | Formalized |
| `lem:block-g-kernel-integrals` — Block (G)-kernels are signed kernel integrals | `ConditionalEntropy.blockGKernelIntegralBridge` | Formalized |
| `lem:block-log-mass-limit` — Block logarithmic-mass splitting and limit | `ConditionalEntropy.blockLogMassLimit` | Formalized |
| `lem:block-log-mass-continuity` — Continuity of logarithmic block-mass kernels | `ConditionalEntropy.blockLogMassKernelContinuous` | Formalized |
| `lem:block-kernel-regularity` — Linearity and continuity of the block kernels | `ConditionalEntropy.blockKernelRegularity` | Formalized |
| `def:two-block-limits` — Two-block limit polynomials | `ConditionalEntropy.twoUpperLogFirst`; `ConditionalEntropy.twoUpperLogSecond`; `ConditionalEntropy.twoLowerLogFirst`; `ConditionalEntropy.twoLowerLogSecond`; `ConditionalEntropy.twoUpperGFirst`; `ConditionalEntropy.twoUpperGSecond`; `ConditionalEntropy.twoLowerGFirst`; `ConditionalEntropy.twoLowerGSecond` | Formalized (split API) |
| `def:three-block-limits` — Three-block cells and limit polynomials | `ConditionalEntropy.threeCellMoment`; `ConditionalEntropy.threeLogFirst`; `ConditionalEntropy.threeLogSecond`; `ConditionalEntropy.threeGFirst`; `ConditionalEntropy.threeGSecond` | Formalized (split API) |
| `lem:two-block-limit-integral-eval` — Evaluation of the two-block limit integrals | `ConditionalEntropy.twoBlockLimitIntegralEval` | Formalized |
| `lem:three-block-limit-integral-eval` — Evaluation of the three-block limit integrals | `ConditionalEntropy.threeBlockLimitIntegralEval` | Formalized |
| `prop:block-localisation` — Two-block and three-block localisation | `ConditionalEntropy.blockLocalization` | Formalized |
| `prop:two-block-localisation` — Two-block localisation interface | `ConditionalEntropy.twoBlockLocalization` | Formalized |
| `prop:three-block-localisation` — Three-block localisation interface | `ConditionalEntropy.threeBlockLocalization` | Formalized |
| `def:shannon-data` — Shannon block data | `ConditionalEntropy.ShannonData`; `ConditionalEntropy.ShannonData.q`; `ConditionalEntropy.shannonScale`; `ConditionalEntropy.shannonLogScale`; `ConditionalEntropy.shannonCount`; `ConditionalEntropy.ShannonIndex` | Formalized (split API) |
| `lem:shannon-q-pos` — Positivity of the complementary Shannon weight | `ConditionalEntropy.ShannonData.q_pos` | Formalized |
| `lem:shannon-log-scale-pos` — Positivity of the Shannon logarithmic scale | `ConditionalEntropy.shannonLogScale_pos` | Formalized |
| `lem:shannon-count-pos` — Positive Shannon block counts | `ConditionalEntropy.shannonCount_pos` | Formalized |
| `def:shannon-index-nonempty` — Nonempty Shannon index and block representative | `ConditionalEntropy.shannonIndexNonempty`; `ConditionalEntropy.shannonRepresentative` | Formalized (split API) |
| `def:shannon-line-data` — Shannon line and its escort | `ConditionalEntropy.shannonLineData`; `ConditionalEntropy.shannonLineRaw`; `ConditionalEntropy.shannonMass`; `ConditionalEntropy.shannonEscort`; `ConditionalEntropy.shannonMean`; `ConditionalEntropy.shannonSecond`; `ConditionalEntropy.shannonVar` | Formalized (split API) |
| `lem:shannon-top-unique-at-zero` — The third Shannon block is strictly maximal at the base point | `ConditionalEntropy.shannonTopUniqueAtZero` | Formalized |
| `def:shannon-kernels` — Named Shannon kernels | `ConditionalEntropy.shannonKOne`; `ConditionalEntropy.shannonKTwo`; `ConditionalEntropy.shannonLogKernel`; `ConditionalEntropy.shannonGKernel`; `ConditionalEntropy.shannonLogMassKernel`; `ConditionalEntropy.shannonPhiCurve`; `ConditionalEntropy.shannonGCurve` | Formalized (split API) |
| `lem:shannon-curve-kernel-bridge` — Shannon curve--kernel bridge | `ConditionalEntropy.shannonCurveKernelBridge` | Formalized |
| `lem:shannon-kernel-integral-bridge` — Shannon derivative--integral and logarithmic splitting bridge | `ConditionalEntropy.shannonKernelIntegralBridge` | Formalized |
| `lem:shannon-kernel-regularity` — Linearity and continuity of the Shannon kernels | `ConditionalEntropy.shannonKernelRegularity` | Formalized |
| `lem:shannon-dedicated-escort` — Dedicated Shannon escort, compact-region, and tail estimates | `ConditionalEntropy.shannonDedicatedEscort` | Formalized |
| `def:shannon-remainder` — Shannon main term and uniform remainder | `ConditionalEntropy.shannonMain`; `ConditionalEntropy.shannonError`; `ConditionalEntropy.shannonCtwoError` | Formalized (split API) |
| `lem:uniform-shannon-expansion` — Uniform Shannon expansion | `ConditionalEntropy.uniformShannonExpansion` | Formalized |
| `lem:shannon-neighbourhood` — Uniform control near the Shannon point | `ConditionalEntropy.shannonNeighbourhood` | Formalized |
| `def:remove-signed-atom` — Signed atom and its removal | `ConditionalEntropy.signedAtom`; `ConditionalEntropy.removeSignedAtom` | Formalized (split API) |
| `lem:remove-signed-atom` — Removing a signed atom | `ConditionalEntropy.removeSignedAtom_spec` | Formalized |
| `lem:signed-witness-integral-bridge` — Witness atoms and the positive lower truncation | `ConditionalEntropy.signedWitnessIntegralBridge` | Formalized |
| `lem:shannon-log-mass` — Shannon-block logarithmic mass derivatives | `ConditionalEntropy.shannonLogMass` | Formalized |
| `def:shannon-localization-targets` — Shannon localization targets | `ConditionalEntropy.shannonTailMoment`; `ConditionalEntropy.shannonLimitFirst`; `ConditionalEntropy.shannonLimitSecond` | Formalized (split API) |
| `prop:shannon-localisation` — Shannon-point localisation | `ConditionalEntropy.shannonLocalization` | Formalized |
| `def:normalized-curvature` — Normalized scalar-line curvature | `ConditionalEntropy.normalizedCurvature` | Formalized |
| `lem:log-curvature-identity` — Logarithmic curvature identity | `ConditionalEntropy.logCurvatureIdentity` | Formalized |
| `lem:log-curvature-obstruction` — Logarithmic curvature limit obstruction | `ConditionalEntropy.logCurvatureObstruction` | Formalized |
| `def:stationarity-package` — Stationarity convergence package | `ConditionalEntropy.StationarityPackage` | Formalized |
| `lem:stationarity-correction` — Exact stationarity correction | `ConditionalEntropy.stationarityCorrection` | Formalized |
| `lem:quasiconvex-second` — Stationary curvature of a quasi-convex function | `ConditionalEntropy.quasiconvexSecond` | Formalized |
| `lem:typed-log-curvature-contradiction` — Typed curvature contradiction from logarithmic kernels | `ConditionalEntropy.typedLogCurvatureContradiction` | Formalized |
| `lem:corrected-stationary-line-obstruction` — Corrected stationary-line obstruction | `ConditionalEntropy.correctedStationaryLineObstruction` | Formalized |
| `prop:positive-necessity` — Positive-measure obstruction | `ConditionalEntropy.positiveNecessity` | Formalized |
| `cor:positive-temperate-probability-necessity` — Positive temperate necessity for probability measures | `ConditionalEntropy.positiveTemperateProbabilityNecessity` | Formalized |
| `prop:negative-shannon-obstruction` — A Shannon atom excludes upper support | `ConditionalEntropy.negativeShannonObstruction` | Formalized |
| `def:negative-truncations` — Positive lower and upper truncations | `ConditionalEntropy.lowerTrunc`; `ConditionalEntropy.upperTrunc` | Formalized (split API) |
| `lem:negative-truncation-bridge` — Negative-witness truncation identities | `ConditionalEntropy.negativeTruncationBridge` | Formalized |
| `prop:truncated-moment` — Truncated-moment obstruction | `ConditionalEntropy.truncatedMoment` | Formalized |
| `prop:one-upper-point` — At most one upper support point | `ConditionalEntropy.oneUpperPoint` | Formalized |
| `prop:negative-temperate-necessity` — Complete negative temperate necessity | `ConditionalEntropy.negativeTemperateNecessity` | Formalized |
| `cor:negative-temperate-probability-necessity` — Negative temperate necessity for probability measures | `ConditionalEntropy.negativeTemperateProbabilityNecessity` | Formalized |
| `prop:negative-tropical-necessity` — Complete negative tropical necessity | `ConditionalEntropy.negativeTropicalNecessity` | Formalized |
| `def:prob-as-pos-cone` — Probability support as a positive cone vector | `ConditionalEntropy.probAsPosCone` | Formalized |
| `lem:prob-as-pos-cone-identities` — Probability-to-cone identities | `ConditionalEntropy.probAsPosConeIdentities` | Formalized |
| `lem:prob-support-nonempty` — A probability vector has nonempty positive support | `ConditionalEntropy.probSupportNonempty` | Formalized |
| `lem:same-support-decomposition` — Decomposition inside a simplex face | `ConditionalEntropy.sameSupportDecomposition` | Formalized |
| `lem:probability-eq-dirac-zero` — Probability supported at zero is the zero Dirac measure | `ConditionalEntropy.probabilityEqDiracZero` | Formalized |
| `prop:positive-tropical-necessity` — Only the support-rank measure survives | `ConditionalEntropy.positiveTropicalNecessity` | Formalized |
| `def:derivation-column-function` — Derivation column function | `ConditionalEntropy.derivationColumn` | Formalized |
| `prop:derivation-necessity` — Derivation necessity | `ConditionalEntropy.derivationNecessity` | Formalized |
| `thm:necessity-bundle` — All necessary parameter conditions | `ConditionalEntropy.necessityBundle` | Formalized |
| `thm:main-classification` — Complete parameter classification | `ConditionalEntropy.mainClassification` | Formalized |
| `def:conditional-entropy-axioms` — Conditional-entropy axiom bundle | `ConditionalEntropy.NonnegativeJointFunctional`; `ConditionalEntropy.FairBitNormalized`; `ConditionalEntropy.CEmbedsMonotone`; `ConditionalEntropy.ConditionalEntropyAxioms` | Formalized (split API) |
| `lem:embedding-lift` — Embedding lift of fixed-row monotonicity | `ConditionalEntropy.embeddingLift` | Formalized |
| `cor:all-conditional-entropy-axioms` — Admissible candidates satisfy the complete axiom bundle | `ConditionalEntropy.allConditionalEntropyAxioms` | Formalized |
