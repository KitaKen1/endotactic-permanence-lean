# Complete modular proof

Entry point: [EndotacticPublication.lean](EndotacticPublication.lean).
The original mathematical library is in [Endotactic/](Endotactic/);
[EndotacticPublication/FCPresentation.lean](EndotacticPublication/FCPresentation.lean) proves the
main Extended Permanence target in the displayed natural-exponent model. It
also proves the measurable-rate, common-box strengthening listed under
[SubContribution](../README.md#appendix-relationship-between-the-original-conjecture-and-the-strengthening).
Both proofs have the exact expanded positive-answer types in the FC-style draft.

Lean v4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
The full proof project depends only on Mathlib; its answer notation elaborates
to True and is checked against the actual FC utility by the publication audit.
The separate FC statement contains the same concrete definitions in one file.
Its compiled definitions and target types are compared against the complete-proof
presentation. [CoordinateBounds.lean](EndotacticPublication/CoordinateBounds.lean)
proves equivalence with the compact-absorption formulation used by the proof library.

~~~bash
lake exe cache get
python3 scripts/build_audit.py
~~~

See the [root README](../README.md) for statements, scope and the mathematical
sketch. Results are in [evidence/](evidence/). Network access may be needed for
first-time dependency setup. The audit is local verification; independent
original-convention review and upstream review remain separate.
