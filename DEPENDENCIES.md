# Formalization dependency graph

The editable graph source is
[`paper/dependency-graph.dot`](paper/dependency-graph.dot). It records the
current final vertical architecture, condensed from Lean imports and explicit
uses of project declarations. An arrow `A → B` means that declarations in the
group `B` use the group `A`, directly or through the displayed condensation;
routine Mathlib dependencies and most intra-group edges are suppressed.

The checked-in SVG and PNG previews are generated from the DOT source. After
editing the graph, run `npm install` and `npm run render:graph` to refresh both
previews.

## Vertical module groups

| Graph node | Lean modules | Role and representative declarations |
|---|---|---|
| Foundation | `FiniteData`, `ParamMeasure`, `Renyi`, `Moments` | Finite probability data, the endpoint-aware parameter type, finite/signed measures, support, and moments. |
| Semiring | `FiniteSemiring`, `FiniteSemiringQuotient` | Conditional direct-sum/tensor semiring and the quotient `CommSemiring` instance `conditionalSemiringCommSemiring`. |
| Channels and order | `FiniteChannels`, `FiniteChannelAlgebra`, `ConditionalSemiringOrder` | Channel composition, `CMRelCone`, the quotient preorder, concrete comparison, and `embeddingLift`. |
| Endpoint calculus and integration | `RenyiProperties`, `LineData`, `LineCalculus`, `EndpointLineCalculus`, `EndpointParameterContinuity`, `IntegratedEntropy`, `SignedWitnesses`, `SignedLineCalculus`, `CompactUniform`, `UniformSignedDCT` | Endpoint-aware Rényi formulas, real-power derivatives, signed differentiation under the integral, and compact-uniform passage. Key declarations include `exactEntropyDerivativeFormulas`, `exactDerivatives`, `signedLogPhiLineDerivativesOfIntegral`, and `uniformDCTSigned`. |
| Shape reductions | `ColumnFunctions`, `ShapeReduction`, `TropicalShapeReduction`, `ULiftInvariance` | Transports conditional monotonicity to the one-column concavity/convexity/quasiconvexity predicates used by necessity. |
| Sufficiency | `FiniteSupportSufficiency`, `GeneralSufficiency`, `Section4Sufficiency` | Finite-support proofs, discretization and closure, and the four final sufficient-condition branches. |
| Block localization | `BlockData`, `BlockEstimates`, `BlockCurves`, `BlockLimitPassage`, `BlockLocalization` | Dominant-block estimates and exact two-/three-block signed-integral limits, including `blockLimitPassage`, `twoBlockLimitIntegralEval`, and `threeBlockLimitIntegralEval`. |
| Localization interfaces | `BlockLocalizationInterfaces`, `LocalizationStationarity` | Exact paper-facing `twoBlockLocalization`, `threeBlockLocalization`, `blockLocalization`, kernel bridges, and `threeBlockGStationarityPackage`. |
| Shannon localization core | `ShannonData`, `ShannonAlgebra`, `ShannonCurves`, `ShannonAtoms`, `ShannonWitnessBridge`, `ShannonKernelRegularity`, `ShannonEscortCalculus`, `ShannonDominance`, `ShannonDedicatedEscort`, `ShannonLocalizationTargets`, `ShannonKernelBridges`, `ShannonKernelRegularityBridge`, `ShannonCurveKernelBridge` | Shannon block data, witness atoms, dedicated escort estimates, kernel regularity, curve bridge, and the four limit targets. |
| Shannon asymptotics | `ShannonLogMass`, `ShannonExpansion` | `shannonLogMass`, `uniformShannonExpansion`, and `shannonNeighbourhood`: the logarithmic-mass decay, rounded three-block expansion, and punctured-neighborhood control consumed by the final localization proof. |
| Shannon localization | `ShannonLocalization` | Final `shannonLocalization` interface: compact-uniform log-kernel and G-kernel convergence for derivative orders one and two. This named integration module is the interface imported by the positive, negative, and negative-tropical Shannon arguments. |
| Necessity measure algebra | `NullThresholds`, `NecessityMeasureAlgebra`, `NecessitySupportAlgebra`, `NecessityMomentPassage`, `NecessityExceptionalMeasureAlgebra`, `NegativeMomentPositivity` | Null-threshold selection, support isolation, truncated moments, monotone-convergence passage, and the exceptional upper atom package. |
| Temperate necessity | `PositiveTemperateNecessity`, `PositiveNecessity`, `NegativeTemperateNecessity`, `NegativeNecessity` | Positive and negative finite-measure arguments, Shannon atom cases, and transport to probability parameters. |
| Tropical necessity | `PositiveTropicalNecessity`, `NegativeTropicalShannonNecessity`, `NegativeTropicalNecessity` | The binary-face Dirac conclusion `positiveTropicalNecessity`; the Shannon obstruction `negativeTropicalUpperAtomZero`; the corrected stationary witnesses `twoUpperSupportPointsTropicalObstruction` and `tropicalTruncatedMoment_of_exceptional`; and the assembled negative conclusion `negativeTropicalNecessity`. |
| Derivation necessity | `DerivationNecessity` | The two-block second-derivative obstruction and support-below-one conclusion. |
| Necessity assembly | `NecessityBundle` | `necessityBundle`, combining all temperate, tropical, and derivation necessity branches. |
| Classification | `MainClassification` | `mainClassification`, combining `necessityBundle` with `Section4Sufficiency`. |
| Candidate law packages | `ConditionalEntropyAxioms`, `CandidateNormalization`, `JointTensorCandidates`, `CandidateEmbeddingInvariance` | Normalization, embedding invariance, tensor additivity, and conditional-monotonicity records for the four candidate families. |
| Full candidate-law assembly | `AllConditionalEntropyAxioms` | `allConditionalEntropyAxioms`, combining the candidate packages, sufficiency, and the original channel lift `embeddingLift`. |

## Critical paths

The proof of classification follows the main vertical path

```text
endpoint calculus and signed integration
  → block localization
  → Shannon core, log-mass, and expansion
  → block/Shannon localization interfaces
  → temperate, tropical, and derivation necessity
  → necessityBundle
  → mainClassification.
```

The algebraic/channel realization follows the parallel path

```text
finite semiring and quotient
  → finite channels and conditional-semiring order
  → candidate normalization/tensor/embedding packages
  → allConditionalEntropyAxioms.
```

`mainClassification` and `allConditionalEntropyAxioms` are intentionally
separate terminal declarations: the former is the necessary-and-sufficient
parameter classification, while the latter verifies the original law package
for each admissible candidate and uses the semiring/channel lift.

For manuscript statement correspondence, see
[`paper/DECLARATION_INDEX.md`](paper/DECLARATION_INDEX.md) and the larger
[`paper/BLUEPRINT_STATEMENT_STATUS.md`](paper/BLUEPRINT_STATEMENT_STATUS.md).
Build and forbidden-token audit results are tracked separately; this document
describes dependencies and does not by itself assert compilation status.
