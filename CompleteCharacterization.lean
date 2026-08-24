import BoundaryProofs.VerifiedKernelBundle
import ConditionalEntropy.AllConditionalEntropyAxioms
import ConditionalEntropy.Conditioning
import ConditionalEntropy.ConditionalSemiringOrder
import ConditionalEntropy.HessianCriterion
import ConditionalEntropy.MainClassification
import ConditionalEntropy.MainTheorem
import ConditionalEntropy.Necessary
import ConditionalEntropy.ParameterizedRemovableShannonQuotient
import ConditionalEntropy.Sufficient

/-!
# A complete characterization of conditional entropies: checked entry point

This module is the repository entry point.  It exposes the closed four-branch
classification `ConditionalEntropy.mainClassification` and the literal
five-axiom candidate bundle
`ConditionalEntropy.allConditionalEntropyAxioms`, together with their complete
dependency trees.
-/
