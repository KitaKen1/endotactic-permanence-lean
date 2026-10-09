# Complete Lean4Web proof

[EndotacticPermanenceLean4Web.lean](EndotacticPermanenceLean4Web.lean) is a complete
single-file proof with only Mathlib imports. It is generated from 83 modular
sources by [make_lean4web.py](../lean/scripts/make_lean4web.py).
It proves the main Extended Permanence target in the displayed natural-exponent
model and the measurable-rate, common-box theorem listed under
[SubContribution](../README.md#appendix-relationship-between-the-original-conjecture-and-the-strengthening).
The final targets use the FC coordinate-bound presentation and include the
Lean equivalences with compact absorption.

Target: Lean v4.35.0-rc4, Mathlib 1f414401f69059aa7eead47b53ee40bd38455eeb.
[source-map.json](source-map.json) records source hashes and line ranges.

<!-- PUBLICATION-LINKS:START -->
**Try it in Lean4Web:** [open the complete proof in one file](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fendotactic-permanence-lean%2Fbfc411af63d0b11b2fd35d6a234249fc56080205%2Flean4web%2FEndotacticPermanenceLean4Web.lean) (Lean **v4.35.0-rc4**).
<!-- PUBLICATION-LINKS:END -->

~~~bash
lake exe cache get
lake --wfail build
~~~

The Lean4Web URL loads the published single-file proof at a fixed commit.

The file is large; the local build is the reproducible verification path.
The browser server is not part of the local audit. Later Lean4Web environment
updates may require a new port. The exact targets and scope are in the
[root README](../README.md).
