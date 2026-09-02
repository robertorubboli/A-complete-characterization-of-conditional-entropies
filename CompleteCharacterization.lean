import BoundaryProofs.VerifiedKernelBundle
import ConditionalEntropy.AllConditionalEntropyAxioms
import ConditionalEntropy.Conditioning
import ConditionalEntropy.ConditionalSemiringOrder
import ConditionalEntropy.FullDetailsAppendixA11
import ConditionalEntropy.FullDetailsAppendixA3A6
import ConditionalEntropy.FullDetailsAppendixStatements
import ConditionalEntropy.FullDetailsStatements
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
dependency trees. It also imports the uniquely named paper-facing declarations
for all numbered environments 4.1--5.10 and A.1--A.15 in the complete-proof
document; the correspondence manifest records the two explicitly qualified
scope boundaries.
-/
