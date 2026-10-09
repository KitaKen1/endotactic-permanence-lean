# Formal Conjectures proposal draft

[EndotacticPermanence.lean](EndotacticPermanence.lean) presents the displayed
natural-exponent Extended Permanence Conjecture as its main target. It then
states the measurable-rate, common-box strengthening listed under
[SubContribution](../README.md#appendix-relationship-between-the-original-conjecture-and-the-strengthening).
Both expanded targets have positive answers outside all quantifiers.
Docstrings give the problem, its source and the answer.

The draft is written for FC submission, with short factual docstrings and
11 `def` declarations and one `Network` structure in one namespace,
`Endotactic`. Its only import is `FormalConjecturesUtil`.
Reactions are indexed by `Fin m`. Both permanence definitions use one positive
number `ε`: every concentration eventually lies in `[ε, ε⁻¹]`.
For the strengthening, `ε` is chosen before the measurable rate path.

Inner products use mathlib's `dotProduct`; stoichiometric coefficients are
cast directly to real numbers. The remaining auxiliary conditions are inlined.

The Lean draft is the source for its presentation.
[make_fc_support.py](../lean/scripts/make_fc_support.py) records metadata without
rewriting it. [source-map.json](source-map.json) records correspondence with the
proof library; the audit checks that all definitions contribute to a conjecture
and compares compiled definitions and target types with the complete proofs.
[CoordinateBounds.lean](../lean/EndotacticPublication/CoordinateBounds.lean)
proves equivalence with compact absorption for positive classes in positive dimension.

There are exactly two intended FC statement stubs. The complete proofs in
[FCPresentation.lean](../lean/EndotacticPublication/FCPresentation.lean) have no holes.
The research-solved tags describe the displayed locally formalized model;
original-convention comparison and upstream acceptance remain outstanding.

<!-- PUBLICATION-LINKS:START -->
**Try it in Lean4Web:** [open the complete proof in one file](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fendotactic-permanence-lean%2Fbfc411af63d0b11b2fd35d6a234249fc56080205%2Flean4web%2FEndotacticPermanenceLean4Web.lean) (Lean **v4.35.0-rc4**).
<!-- PUBLICATION-LINKS:END -->

The local utility pin is 89294ea02bd7cd678d59984add52cb4baef3dbf4 (Lean v4.33.1).
[build_audit.py](../lean/scripts/build_audit.py) checks FC linters, definition
dependencies and the correspondence of both targets with complete proofs.
[make_fc_proof.py](../lean/scripts/make_fc_proof.py) adapts the proof-library
interface outside the draft, using network conversion and the coordinate-bound
equivalences. It generates the complete-proof presentation from the draft.
This does not run the latest upstream CI.
