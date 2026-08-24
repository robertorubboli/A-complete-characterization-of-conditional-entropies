import ConditionalEntropy.AllConditionalEntropyAxioms
import ConditionalEntropy.MainClassification

/-!
# Paper-facing theorem entry point

This compatibility module re-exports the two closed paper-facing results:

* `mainClassification`, the hypothesis-free necessary-and-sufficient
  parameter classification for each probability measure; and
* `allConditionalEntropyAxioms`, the original five-axiom semiring/channel
  package for every admissible candidate.

The former finite-profile placeholder implications have been superseded by
the measure-level theorems in `NecessityBundle` and `MainClassification`.
-/
