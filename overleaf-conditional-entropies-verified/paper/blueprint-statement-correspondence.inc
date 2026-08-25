% Generated correspondence appendix for the 152 labeled statements in the
% formalization blueprint. Keep this file synchronized with
% BLUEPRINT_STATEMENT_STATUS.md and blueprint-sections-4-5.tex.

% REVTeX 4.2 currently fails on fixed-width p{...} columns with recent LaTeX
% kernels. Plain l columns containing top-aligned minipages give the same
% wrapping without invoking the incompatible p-column parser.
\providecommand{\BlueprintStatement}[2]{\path{#1}: #2}
\providecommand{\LeanDecl}[1]{\path{#1}}

\small
\begin{longtable}{@{}%
  >{\begin{minipage}[t]{0.30\textwidth}\raggedright\sloppy}l<{\end{minipage}}%
  >{\begin{minipage}[t]{0.43\textwidth}\raggedright\sloppy}l<{\end{minipage}}%
  l@{}}
\caption{Statement-by-statement correspondence between the manuscript blueprint and the Lean formalization.}
\label{tab:blueprint-statement-correspondence}\\
\toprule
\textbf{Manuscript statement} & \textbf{Lean declaration} & \textbf{Status} \\
\midrule
\endfirsthead
\toprule
\textbf{Manuscript statement} & \textbf{Lean declaration} & \textbf{Status} \\
\midrule
\endhead
\bottomrule
\endfoot
\BlueprintStatement{lem:origin-extension}{Extension from the punctured cone} & \LeanDecl{ConditionalEntropy.originExtension} & Formalized \\
\BlueprintStatement{lem:punctured-cone-convex}{Convexity of the punctured nonnegative cone} & \LeanDecl{ConditionalEntropy.puncturedConeConvex} & Formalized \\
\BlueprintStatement{lem:composition-rule}{Monotone composition rule} & \LeanDecl{ConditionalEntropy.compositionRule} & Formalized \\
\BlueprintStatement{lem:cone-composition-rule}{Monotone composition on the punctured cone} & \LeanDecl{ConditionalEntropy.coneCompositionRule} & Formalized \\
\BlueprintStatement{lem:finite-holder}{Finite H\"older inequality} & \LeanDecl{ConditionalEntropy.finiteHolder} & Formalized \\
\BlueprintStatement{lem:power-curvature}{Power-mean curvature} & \LeanDecl{ConditionalEntropy.powerCurvature} & Formalized \\
\BlueprintStatement{lem:parameter-power-curvature}{Compactified power-mean bridge} & \LeanDecl{ConditionalEntropy.parameterPowerCurvature} & Formalized \\
\BlueprintStatement{def:hessian-quad}{Hessian quadratic form} & \LeanDecl{ConditionalEntropy.hessianQuad} & Formalized \\
\BlueprintStatement{lem:hessian-sign-criterion}{Hessian sign criterion} & \LeanDecl{ConditionalEntropy.hessianSignCriterion} & Formalized \\
\BlueprintStatement{lem:real-rpow-calculus}{Positive-base real-power calculus} & \LeanDecl{ConditionalEntropy.realRpowCalculus} & Formalized \\
\BlueprintStatement{lem:monomial-curvature}{Curvature of an affine monomial} & \LeanDecl{ConditionalEntropy.affineMonomialCurvaturePackage} & Formalized \\
\BlueprintStatement{lem:finite-support-enumeration}{Enumeration of a finite probability support} & \LeanDecl{ConditionalEntropy.finiteSupportEnumeration} & Formalized \\
\BlueprintStatement{lem:finite-support-dirac}{Finite-support measure decomposition} & \LeanDecl{ConditionalEntropy.finiteSupportDirac} & Formalized \\
\BlueprintStatement{prop:finite-sufficiency}{Finite-support sufficiency} & \LeanDecl{ConditionalEntropy.finiteSufficiency} & Formalized \\
\BlueprintStatement{prop:general-sufficiency}{General temperate sufficiency} & \LeanDecl{ConditionalEntropy.generalSufficiency} & Formalized \\
\BlueprintStatement{cor:finite-t-sufficiency}{Finite-$t$ sufficiency} & \LeanDecl{ConditionalEntropy.finiteTSufficiency} & Formalized \\
\BlueprintStatement{prop:negative-tropical-sufficiency}{Negative tropical sufficiency} & \LeanDecl{ConditionalEntropy.negativeTropicalSufficiency} & Formalized \\
\BlueprintStatement{lem:positive-tropical-component}{Positive tropical component formula} & \LeanDecl{ConditionalEntropy.positiveTropicalComponent} & Formalized \\
\BlueprintStatement{prop:positive-tropical-sufficiency}{Positive tropical sufficiency} & \LeanDecl{ConditionalEntropy.positiveTropicalSufficiency} & Formalized \\
\BlueprintStatement{def:derivation-family}{Derivation polymorphic family} & \LeanDecl{ConditionalEntropy.derivationFamily} & Formalized \\
\BlueprintStatement{prop:derivation-sufficiency}{Derivation sufficiency} & \LeanDecl{ConditionalEntropy.derivationSufficiency} & Formalized \\
\BlueprintStatement{def:signed-column-functions}{Signed-measure column functions} & \LeanDecl{ConditionalEntropy.integratedEntropySigned}; \LeanDecl{ConditionalEntropy.PhiSigned}; \LeanDecl{ConditionalEntropy.GSigned} & Formalized (split API) \\
\BlueprintStatement{def:signed-witness-predicates}{Positive and negative signed witnesses} & \LeanDecl{ConditionalEntropy.positiveSigned}; \LeanDecl{ConditionalEntropy.negativeSigned}; \LeanDecl{ConditionalEntropy.PosPhiConcave}; \LeanDecl{ConditionalEntropy.NegPhiConvex}; \LeanDecl{ConditionalEntropy.NegGQuasiconvex} & Formalized (split API) \\
\BlueprintStatement{lem:signed-witness-bridge}{Scaling, total variation, support, and atoms of witnesses} & \LeanDecl{ConditionalEntropy.signedWitnessBridge} & Formalized \\
\BlueprintStatement{lem:signed-scalar-column-bridge}{Signed-scalar bridge to the candidate column functions} & \LeanDecl{ConditionalEntropy.signedScalarColumnBridge} & Formalized \\
\BlueprintStatement{def:finite-param}{Embedding a finite real order} & \LeanDecl{ConditionalEntropy.finiteParam} & Formalized \\
\BlueprintStatement{def:positive-line-data}{Positive multiplicative line data} & \LeanDecl{ConditionalEntropy.PositiveLineData} & Formalized \\
\BlueprintStatement{def:positive-line-raw}{Raw multiplicative line} & \LeanDecl{ConditionalEntropy.lineRaw} & Formalized \\
\BlueprintStatement{def:positive-line-predicate}{Positivity predicate for a line} & \LeanDecl{ConditionalEntropy.LinePositive} & Formalized \\
\BlueprintStatement{lem:line-positive-zero}{The base point of a positive line is positive} & \LeanDecl{ConditionalEntropy.linePositiveZero} & Formalized \\
\BlueprintStatement{def:line-cone}{Proof-carrying cone versions of a positive line} & \LeanDecl{ConditionalEntropy.lineCone}; \LeanDecl{ConditionalEntropy.linePosCone}; \LeanDecl{ConditionalEntropy.lineConeTotal}; \LeanDecl{ConditionalEntropy.linePosConeTotal} & Formalized (split API) \\
\BlueprintStatement{def:positive-line-prob}{Total normalized line} & \LeanDecl{ConditionalEntropy.lineProb} & Formalized \\
\BlueprintStatement{def:scalar-qcvx-on}{Scalar quasiconvexity on a set} & \LeanDecl{ConditionalEntropy.ScalarQCvxOn} & Formalized \\
\BlueprintStatement{lem:cone-affine-line-bridge}{Restricting cone curvature to a positive affine line} & \LeanDecl{ConditionalEntropy.coneAffineLineBridge} & Formalized \\
\BlueprintStatement{def:entropy-line}{Entropy line} & \LeanDecl{ConditionalEntropy.entropyLine} & Formalized \\
\BlueprintStatement{def:entropy-line-first}{First entropy line derivative} & \LeanDecl{ConditionalEntropy.entropyLineFirst} & Formalized \\
\BlueprintStatement{def:entropy-line-second}{Second entropy line derivative} & \LeanDecl{ConditionalEntropy.entropyLineSecond} & Formalized \\
\BlueprintStatement{def:escort-weight}{Escort weight} & \LeanDecl{ConditionalEntropy.escortWeight} & Formalized \\
\BlueprintStatement{def:effective-line-velocity}{Effective line velocity} & \LeanDecl{ConditionalEntropy.effectiveVelocity} & Formalized \\
\BlueprintStatement{def:escort-mean}{Escort mean} & \LeanDecl{ConditionalEntropy.escortMean} & Formalized \\
\BlueprintStatement{def:escort-second}{Escort second moment} & \LeanDecl{ConditionalEntropy.escortSecond} & Formalized \\
\BlueprintStatement{def:escort-variance}{Escort variance} & \LeanDecl{ConditionalEntropy.escortVar} & Formalized \\
\BlueprintStatement{def:fixed-max-coordinate}{Fixed maximal-coordinate condition} & \LeanDecl{ConditionalEntropy.FixedMaxCoordinate} & Formalized \\
\BlueprintStatement{lem:positivity-intervals}{Common positivity and maximal-coordinate intervals} & \LeanDecl{ConditionalEntropy.exists\_uniform\_coordinate\_bound}; \LeanDecl{ConditionalEntropy.exists\_uniform\_shannonVelocity\_bound}; \LeanDecl{ConditionalEntropy.exists\_fixedMaxCoordinate\_blockLine}; \LeanDecl{ConditionalEntropy.exists\_fixedMaxCoordinate\_shannonLine} & Formalized (split API) \\
\BlueprintStatement{def:iterated-deriv}{Iterated one-variable derivative} & \LeanDecl{ConditionalEntropy.iteratedDeriv} & Formalized \\
\BlueprintStatement{def:lambda-deriv}{Iterated derivative in the second variable} & \LeanDecl{ConditionalEntropy.lambdaDeriv} & Formalized \\
\BlueprintStatement{def:alpha-lambda-deriv}{Mixed parameter--line derivative} & \LeanDecl{ConditionalEntropy.alphaLambdaDeriv} & Formalized \\
\BlueprintStatement{def:removable-shannon-quotient}{Removable Shannon quotient} & \LeanDecl{ConditionalEntropy.removableShannonQuotient} & Formalized \\
\BlueprintStatement{lem:parameterized-removable-quotient}{Parameterized removable quotient at the Shannon point} & \LeanDecl{ConditionalEntropy.parameterizedRemovableShannonQuotient} & Formalized \\
\BlueprintStatement{lem:signed-integral-differentiate-twice}{Twice differentiating a finite signed-measure integral} & \LeanDecl{ConditionalEntropy.signedIntegral\_differentiate\_twice} & Formalized \\
\BlueprintStatement{def:shannon-line-slope}{Shannon line slope} & \LeanDecl{ConditionalEntropy.shannonLineSlope} & Formalized \\
\BlueprintStatement{lem:exact-derivatives}{Exact entropy derivatives} & \LeanDecl{ConditionalEntropy.exactDerivatives} & Formalized \\
\BlueprintStatement{def:integrated-entropy-line}{Integrated entropy along a line} & \LeanDecl{ConditionalEntropy.integratedEntropyLine} & Formalized \\
\BlueprintStatement{def:signed-log-phi-line}{Signed logarithmic column line} & \LeanDecl{ConditionalEntropy.signedLogPhiLine} & Formalized \\
\BlueprintStatement{lem:signed-line-column-bridge}{Exact bridge from line kernels to signed column functions} & \LeanDecl{ConditionalEntropy.signedLineColumnBridge} & Formalized \\
\BlueprintStatement{lem:differentiate-integral}{Differentiation through the parameter integral} & \LeanDecl{ConditionalEntropy.signedIntegral\_differentiate\_twice}; \LeanDecl{ConditionalEntropy.signedLogPhiLineDerivativesOfIntegral} & Formalized (split API) \\
\BlueprintStatement{lem:null-thresholds}{Null thresholds} & \LeanDecl{ConditionalEntropy.nullThresholds} & Formalized \\
\BlueprintStatement{lem:two-upper-null-thresholds}{Two finite null thresholds between upper parameters} & \LeanDecl{ConditionalEntropy.twoUpperNullThresholds} & Formalized \\
\BlueprintStatement{lem:support-strict-integral}{Support gives strict weighted mass} & \LeanDecl{ConditionalEntropy.supportStrictIntegral} & Formalized \\
\BlueprintStatement{lem:scalar-measure-support}{Scalar measure support and null points} & \LeanDecl{ConditionalEntropy.scalarMeasureSupport} & Formalized \\
\BlueprintStatement{def:block-index}{Finite dependent block carrier} & \LeanDecl{ConditionalEntropy.BlockIndex} & Formalized \\
\BlueprintStatement{def:block-vector}{Constant-on-block vector} & \LeanDecl{ConditionalEntropy.blockVec} & Formalized \\
\BlueprintStatement{def:block-data}{Asymptotic block data} & \LeanDecl{ConditionalEntropy.BlockData} & Formalized \\
\BlueprintStatement{lem:block-count-pos}{Positive block counts} & \LeanDecl{ConditionalEntropy.blockCount\_pos} & Formalized \\
\BlueprintStatement{def:block-carrier-nonempty}{Nonempty block-carrier instance} & \LeanDecl{ConditionalEntropy.blockCarrierNonempty} & Formalized \\
\BlueprintStatement{def:block-index-nonempty}{Nonempty arbitrary block index} & \LeanDecl{ConditionalEntropy.blockIndexNonempty} & Formalized \\
\BlueprintStatement{def:block-max}{Maximum of a nonempty block vector} & \LeanDecl{ConditionalEntropy.blockMax} & Formalized \\
\BlueprintStatement{def:block-line-data}{Typed block line} & \LeanDecl{ConditionalEntropy.blockBase}; \LeanDecl{ConditionalEntropy.blockVelocity}; \LeanDecl{ConditionalEntropy.blockLineData}; \LeanDecl{ConditionalEntropy.blockLineRaw} & Formalized (split API) \\
\BlueprintStatement{def:block-kernels}{Block exponents, escort weights, and derivative kernels} & \LeanDecl{ConditionalEntropy.blockExponent}; \LeanDecl{ConditionalEntropy.blockContribution}; \LeanDecl{ConditionalEntropy.blockEscort}; \LeanDecl{ConditionalEntropy.blockEscortMean}; \LeanDecl{ConditionalEntropy.blockEscortSecond}; \LeanDecl{ConditionalEntropy.blockEscortVar}; \LeanDecl{ConditionalEntropy.blockKernelFirst}; \LeanDecl{ConditionalEntropy.blockKernelSecond} & Formalized (split API) \\
\BlueprintStatement{lem:block-vector-formulas}{Block-vector finite-sum formulas} & \LeanDecl{ConditionalEntropy.blockVectorFormulas} & Formalized \\
\BlueprintStatement{lem:rounding}{Rounding estimates} & \LeanDecl{ConditionalEntropy.roundingEstimates} & Formalized \\
\BlueprintStatement{lem:dominant-block}{Dominant-block escort estimate} & \LeanDecl{ConditionalEntropy.dominantBlock} & Formalized \\
\BlueprintStatement{lem:near-shannon-dominant}{Near-Shannon cancellation for a dominant block} & \LeanDecl{ConditionalEntropy.nearShannonDominant} & Formalized \\
\BlueprintStatement{lem:large-alpha-tail}{Large-order tail bound} & \LeanDecl{ConditionalEntropy.largeAlphaTail} & Formalized \\
\BlueprintStatement{def:block-limit-kernels}{Pointwise limit kernels for a block family} & \LeanDecl{ConditionalEntropy.blockLimitFirst}; \LeanDecl{ConditionalEntropy.blockLimitSecond} & Formalized (split API) \\
\BlueprintStatement{prop:block-limit-passage}{Uniform passage to the block limit} & \LeanDecl{ConditionalEntropy.blockLimitPassage} & Formalized \\
\BlueprintStatement{def:special-block-data}{Specialized block data and signed truncations} & \LeanDecl{ConditionalEntropy.twoBlockData}; \LeanDecl{ConditionalEntropy.threeBlockData}; \LeanDecl{ConditionalEntropy.lowerMoment}; \LeanDecl{ConditionalEntropy.upperMoment} & Formalized (split API) \\
\BlueprintStatement{def:special-block-top-unique}{Unique top blocks for the special families} & \LeanDecl{ConditionalEntropy.twoBlockTopUnique}; \LeanDecl{ConditionalEntropy.threeBlockTopUnique} & Formalized (split API) \\
\BlueprintStatement{def:block-dominance-maps}{Total two-block and three-block dominance maps} & \LeanDecl{ConditionalEntropy.twoDominanceMap}; \LeanDecl{ConditionalEntropy.threeDominanceMap} & Formalized (split API) \\
\BlueprintStatement{lem:two-block-dominance-package}{Exact two-block dominance package} & \LeanDecl{ConditionalEntropy.twoBlockDominancePackage} & Formalized \\
\BlueprintStatement{lem:three-block-dominance-package}{Exact three-block dominance package} & \LeanDecl{ConditionalEntropy.threeBlockDominancePackage} & Formalized \\
\BlueprintStatement{lem:two-order-one-dominance}{Unique order-one block for the two-block family} & \LeanDecl{ConditionalEntropy.twoOrderOneDominancePackage} & Formalized \\
\BlueprintStatement{lem:three-order-one-dominance}{Unique order-one block for the three-block family} & \LeanDecl{ConditionalEntropy.threeOrderOneDominant} & Formalized \\
\BlueprintStatement{def:block-log-g-kernels}{Block logarithmic and norm-free kernels} & \LeanDecl{ConditionalEntropy.blockLogKernel}; \LeanDecl{ConditionalEntropy.blockGKernel} & Formalized (split API) \\
\BlueprintStatement{lem:compact-uniform-eval}{Evaluation of compact-uniform convergence} & \LeanDecl{ConditionalEntropy.compactUniformEval} & Formalized \\
\BlueprintStatement{lem:compact-uniform-add}{Addition closure for compact-uniform convergence} & \LeanDecl{ConditionalEntropy.compactUniformConverges\_add} & Formalized \\
\BlueprintStatement{lem:compact-uniform-singleton}{Evaluation on a singleton} & \LeanDecl{ConditionalEntropy.compactUniformSingleton} & Formalized \\
\BlueprintStatement{lem:subtype-uniform-error-bridge}{Subtype bridge for uniform signed-integral errors} & \LeanDecl{ConditionalEntropy.subtypeUniformErrorBridge} & Formalized \\
\BlueprintStatement{lem:block-curve-kernel-bridge}{Block curve--kernel bridge} & \LeanDecl{ConditionalEntropy.blockCurveKernelBridge} & Formalized \\
\BlueprintStatement{lem:block-g-kernel-integrals}{Block (G)-kernels are signed kernel integrals} & \LeanDecl{ConditionalEntropy.blockGKernelIntegralBridge} & Formalized \\
\BlueprintStatement{lem:block-log-mass-limit}{Block logarithmic-mass splitting and limit} & \LeanDecl{ConditionalEntropy.blockLogMassLimit} & Formalized \\
\BlueprintStatement{lem:block-log-mass-continuity}{Continuity of logarithmic block-mass kernels} & \LeanDecl{ConditionalEntropy.blockLogMassKernelContinuous} & Formalized \\
\BlueprintStatement{lem:block-kernel-regularity}{Linearity and continuity of the block kernels} & \LeanDecl{ConditionalEntropy.blockKernelRegularity} & Formalized \\
\BlueprintStatement{def:two-block-limits}{Two-block limit polynomials} & \LeanDecl{ConditionalEntropy.twoUpperLogFirst}; \LeanDecl{ConditionalEntropy.twoUpperLogSecond}; \LeanDecl{ConditionalEntropy.twoLowerLogFirst}; \LeanDecl{ConditionalEntropy.twoLowerLogSecond}; \LeanDecl{ConditionalEntropy.twoUpperGFirst}; \LeanDecl{ConditionalEntropy.twoUpperGSecond}; \LeanDecl{ConditionalEntropy.twoLowerGFirst}; \LeanDecl{ConditionalEntropy.twoLowerGSecond} & Formalized (split API) \\
\BlueprintStatement{def:three-block-limits}{Three-block cells and limit polynomials} & \LeanDecl{ConditionalEntropy.threeCellMoment}; \LeanDecl{ConditionalEntropy.threeLogFirst}; \LeanDecl{ConditionalEntropy.threeLogSecond}; \LeanDecl{ConditionalEntropy.threeGFirst}; \LeanDecl{ConditionalEntropy.threeGSecond} & Formalized (split API) \\
\BlueprintStatement{lem:two-block-limit-integral-eval}{Evaluation of the two-block limit integrals} & \LeanDecl{ConditionalEntropy.twoBlockLimitIntegralEval} & Formalized \\
\BlueprintStatement{lem:three-block-limit-integral-eval}{Evaluation of the three-block limit integrals} & \LeanDecl{ConditionalEntropy.threeBlockLimitIntegralEval} & Formalized \\
\BlueprintStatement{prop:block-localisation}{Two-block and three-block localisation} & \LeanDecl{ConditionalEntropy.blockLocalization} & Formalized \\
\BlueprintStatement{prop:two-block-localisation}{Two-block localisation interface} & \LeanDecl{ConditionalEntropy.twoBlockLocalization} & Formalized \\
\BlueprintStatement{prop:three-block-localisation}{Three-block localisation interface} & \LeanDecl{ConditionalEntropy.threeBlockLocalization} & Formalized \\
\BlueprintStatement{def:shannon-data}{Shannon block data} & \LeanDecl{ConditionalEntropy.ShannonData}; \LeanDecl{ConditionalEntropy.ShannonData.q}; \LeanDecl{ConditionalEntropy.shannonScale}; \LeanDecl{ConditionalEntropy.shannonLogScale}; \LeanDecl{ConditionalEntropy.shannonCount}; \LeanDecl{ConditionalEntropy.ShannonIndex} & Formalized (split API) \\
\BlueprintStatement{lem:shannon-q-pos}{Positivity of the complementary Shannon weight} & \LeanDecl{ConditionalEntropy.ShannonData.q\_pos} & Formalized \\
\BlueprintStatement{lem:shannon-log-scale-pos}{Positivity of the Shannon logarithmic scale} & \LeanDecl{ConditionalEntropy.shannonLogScale\_pos} & Formalized \\
\BlueprintStatement{lem:shannon-count-pos}{Positive Shannon block counts} & \LeanDecl{ConditionalEntropy.shannonCount\_pos} & Formalized \\
\BlueprintStatement{def:shannon-index-nonempty}{Nonempty Shannon index and block representative} & \LeanDecl{ConditionalEntropy.shannonIndexNonempty}; \LeanDecl{ConditionalEntropy.shannonRepresentative} & Formalized (split API) \\
\BlueprintStatement{def:shannon-line-data}{Shannon line and its escort} & \LeanDecl{ConditionalEntropy.shannonLineData}; \LeanDecl{ConditionalEntropy.shannonLineRaw}; \LeanDecl{ConditionalEntropy.shannonMass}; \LeanDecl{ConditionalEntropy.shannonEscort}; \LeanDecl{ConditionalEntropy.shannonMean}; \LeanDecl{ConditionalEntropy.shannonSecond}; \LeanDecl{ConditionalEntropy.shannonVar} & Formalized (split API) \\
\BlueprintStatement{lem:shannon-top-unique-at-zero}{The third Shannon block is strictly maximal at the base point} & \LeanDecl{ConditionalEntropy.shannonTopUniqueAtZero} & Formalized \\
\BlueprintStatement{def:shannon-kernels}{Named Shannon kernels} & \LeanDecl{ConditionalEntropy.shannonKOne}; \LeanDecl{ConditionalEntropy.shannonKTwo}; \LeanDecl{ConditionalEntropy.shannonLogKernel}; \LeanDecl{ConditionalEntropy.shannonGKernel}; \LeanDecl{ConditionalEntropy.shannonLogMassKernel}; \LeanDecl{ConditionalEntropy.shannonPhiCurve}; \LeanDecl{ConditionalEntropy.shannonGCurve} & Formalized (split API) \\
\BlueprintStatement{lem:shannon-curve-kernel-bridge}{Shannon curve--kernel bridge} & \LeanDecl{ConditionalEntropy.shannonCurveKernelBridge} & Formalized \\
\BlueprintStatement{lem:shannon-kernel-integral-bridge}{Shannon derivative--integral and logarithmic splitting bridge} & \LeanDecl{ConditionalEntropy.shannonKernelIntegralBridge} & Formalized \\
\BlueprintStatement{lem:shannon-kernel-regularity}{Linearity and continuity of the Shannon kernels} & \LeanDecl{ConditionalEntropy.shannonKernelRegularity} & Formalized \\
\BlueprintStatement{lem:shannon-dedicated-escort}{Dedicated Shannon escort, compact-region, and tail estimates} & \LeanDecl{ConditionalEntropy.shannonDedicatedEscort} & Formalized \\
\BlueprintStatement{def:shannon-remainder}{Shannon main term and uniform remainder} & \LeanDecl{ConditionalEntropy.shannonMain}; \LeanDecl{ConditionalEntropy.shannonError}; \LeanDecl{ConditionalEntropy.shannonCtwoError} & Formalized (split API) \\
\BlueprintStatement{lem:uniform-shannon-expansion}{Uniform Shannon expansion} & \LeanDecl{ConditionalEntropy.uniformShannonExpansion} & Formalized \\
\BlueprintStatement{lem:shannon-neighbourhood}{Uniform control near the Shannon point} & \LeanDecl{ConditionalEntropy.shannonNeighbourhood} & Formalized \\
\BlueprintStatement{def:remove-signed-atom}{Signed atom and its removal} & \LeanDecl{ConditionalEntropy.signedAtom}; \LeanDecl{ConditionalEntropy.removeSignedAtom} & Formalized (split API) \\
\BlueprintStatement{lem:remove-signed-atom}{Removing a signed atom} & \LeanDecl{ConditionalEntropy.removeSignedAtom\_spec} & Formalized \\
\BlueprintStatement{lem:signed-witness-integral-bridge}{Witness atoms and the positive lower truncation} & \LeanDecl{ConditionalEntropy.signedWitnessIntegralBridge} & Formalized \\
\BlueprintStatement{lem:shannon-log-mass}{Shannon-block logarithmic mass derivatives} & \LeanDecl{ConditionalEntropy.shannonLogMass} & Formalized \\
\BlueprintStatement{def:shannon-localization-targets}{Shannon localization targets} & \LeanDecl{ConditionalEntropy.shannonTailMoment}; \LeanDecl{ConditionalEntropy.shannonLimitFirst}; \LeanDecl{ConditionalEntropy.shannonLimitSecond} & Formalized (split API) \\
\BlueprintStatement{prop:shannon-localisation}{Shannon-point localisation} & \LeanDecl{ConditionalEntropy.shannonLocalization} & Formalized \\
\BlueprintStatement{def:normalized-curvature}{Normalized scalar-line curvature} & \LeanDecl{ConditionalEntropy.normalizedCurvature} & Formalized \\
\BlueprintStatement{lem:log-curvature-identity}{Logarithmic curvature identity} & \LeanDecl{ConditionalEntropy.logCurvatureIdentity} & Formalized \\
\BlueprintStatement{lem:log-curvature-obstruction}{Logarithmic curvature limit obstruction} & \LeanDecl{ConditionalEntropy.logCurvatureObstruction} & Formalized \\
\BlueprintStatement{def:stationarity-package}{Stationarity convergence package} & \LeanDecl{ConditionalEntropy.StationarityPackage} & Formalized \\
\BlueprintStatement{lem:stationarity-correction}{Exact stationarity correction} & \LeanDecl{ConditionalEntropy.stationarityCorrection} & Formalized \\
\BlueprintStatement{lem:quasiconvex-second}{Stationary curvature of a quasi-convex function} & \LeanDecl{ConditionalEntropy.quasiconvexSecond} & Formalized \\
\BlueprintStatement{lem:typed-log-curvature-contradiction}{Typed curvature contradiction from logarithmic kernels} & \LeanDecl{ConditionalEntropy.typedLogCurvatureContradiction} & Formalized \\
\BlueprintStatement{lem:corrected-stationary-line-obstruction}{Corrected stationary-line obstruction} & \LeanDecl{ConditionalEntropy.correctedStationaryLineObstruction} & Formalized \\
\BlueprintStatement{prop:positive-necessity}{Positive-measure obstruction} & \LeanDecl{ConditionalEntropy.positiveNecessity} & Formalized \\
\BlueprintStatement{cor:positive-temperate-probability-necessity}{Positive temperate necessity for probability measures} & \LeanDecl{ConditionalEntropy.positiveTemperateProbabilityNecessity} & Formalized \\
\BlueprintStatement{prop:negative-shannon-obstruction}{A Shannon atom excludes upper support} & \LeanDecl{ConditionalEntropy.negativeShannonObstruction} & Formalized \\
\BlueprintStatement{def:negative-truncations}{Positive lower and upper truncations} & \LeanDecl{ConditionalEntropy.lowerTrunc}; \LeanDecl{ConditionalEntropy.upperTrunc} & Formalized (split API) \\
\BlueprintStatement{lem:negative-truncation-bridge}{Negative-witness truncation identities} & \LeanDecl{ConditionalEntropy.negativeTruncationBridge} & Formalized \\
\BlueprintStatement{prop:truncated-moment}{Truncated-moment obstruction} & \LeanDecl{ConditionalEntropy.truncatedMoment} & Formalized \\
\BlueprintStatement{prop:one-upper-point}{At most one upper support point} & \LeanDecl{ConditionalEntropy.oneUpperPoint} & Formalized \\
\BlueprintStatement{prop:negative-temperate-necessity}{Complete negative temperate necessity} & \LeanDecl{ConditionalEntropy.negativeTemperateNecessity} & Formalized \\
\BlueprintStatement{cor:negative-temperate-probability-necessity}{Negative temperate necessity for probability measures} & \LeanDecl{ConditionalEntropy.negativeTemperateProbabilityNecessity} & Formalized \\
\BlueprintStatement{prop:negative-tropical-necessity}{Complete negative tropical necessity} & \LeanDecl{ConditionalEntropy.negativeTropicalNecessity} & Formalized \\
\BlueprintStatement{def:prob-as-pos-cone}{Probability support as a positive cone vector} & \LeanDecl{ConditionalEntropy.probAsPosCone} & Formalized \\
\BlueprintStatement{lem:prob-as-pos-cone-identities}{Probability-to-cone identities} & \LeanDecl{ConditionalEntropy.probAsPosConeIdentities} & Formalized \\
\BlueprintStatement{lem:prob-support-nonempty}{A probability vector has nonempty positive support} & \LeanDecl{ConditionalEntropy.probSupportNonempty} & Formalized \\
\BlueprintStatement{lem:same-support-decomposition}{Decomposition inside a simplex face} & \LeanDecl{ConditionalEntropy.sameSupportDecomposition} & Formalized \\
\BlueprintStatement{lem:probability-eq-dirac-zero}{Probability supported at zero is the zero Dirac measure} & \LeanDecl{ConditionalEntropy.probabilityEqDiracZero} & Formalized \\
\BlueprintStatement{prop:positive-tropical-necessity}{Only the support-rank measure survives} & \LeanDecl{ConditionalEntropy.positiveTropicalNecessity} & Formalized \\
\BlueprintStatement{def:derivation-column-function}{Derivation column function} & \LeanDecl{ConditionalEntropy.derivationColumn} & Formalized \\
\BlueprintStatement{prop:derivation-necessity}{Derivation necessity} & \LeanDecl{ConditionalEntropy.derivationNecessity} & Formalized \\
\BlueprintStatement{thm:necessity-bundle}{All necessary parameter conditions} & \LeanDecl{ConditionalEntropy.necessityBundle} & Formalized \\
\BlueprintStatement{thm:main-classification}{Complete parameter classification} & \LeanDecl{ConditionalEntropy.mainClassification} & Formalized \\
\BlueprintStatement{def:conditional-entropy-axioms}{Conditional-entropy axiom bundle} & \LeanDecl{ConditionalEntropy.NonnegativeJointFunctional}; \LeanDecl{ConditionalEntropy.FairBitNormalized}; \LeanDecl{ConditionalEntropy.CEmbedsMonotone}; \LeanDecl{ConditionalEntropy.ConditionalEntropyAxioms} & Formalized (split API) \\
\BlueprintStatement{lem:embedding-lift}{Embedding lift of fixed-row monotonicity} & \LeanDecl{ConditionalEntropy.embeddingLift} & Formalized \\
\BlueprintStatement{cor:all-conditional-entropy-axioms}{Admissible candidates satisfy the complete axiom bundle} & \LeanDecl{ConditionalEntropy.allConditionalEntropyAxioms} & Formalized \\
\end{longtable}
\normalsize
