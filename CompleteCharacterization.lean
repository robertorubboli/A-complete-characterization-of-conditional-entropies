import BoundaryProofs.VerifiedKernelBundle
import ConditionalEntropy.Cone
import ConditionalEntropy.Conditioning
import ConditionalEntropy.MainTheorem

/-!
# A complete characterization of conditional entropies: checked entry point

This module is the repository entry point.  It exposes the independently
kernel-checked finite algebra, order, stationarity, midpoint, dominant-block,
and pointwise-limit results together with the explicitly labelled finite-profile
implications.

It deliberately does not declare the manuscript's `mainClassification`:
the exact statement ledger in `paper/BLUEPRINT_STATEMENT_STATUS.md` records the
measure-theoretic and localization results that still require formalization.
-/
