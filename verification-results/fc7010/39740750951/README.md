# FC #7010 verification on main

The [CI run on main](https://github.com/KitaKen1/endotactic-permanence-lean/actions/runs/39740750951)
completed successfully. Its executed harness commit is
[`050430c825ebe9c8aac572fa4af57ad438d7b5ab`](https://github.com/KitaKen1/endotactic-permanence-lean/tree/050430c825ebe9c8aac572fa4af57ad438d7b5ab/leanWithComparator).
This directory preserves the generated evidence. The evidence publication commit
is separate from the executed harness commit.

| Original theorem | Statement and definitions | Permitted axioms | Kernel replay |
|---|---|---|---|
| `EndotacticFC.extended_permanence` | PASS | PASS | PASS |
| `EndotacticFC.measurable_extended_permanence` | PASS | PASS | PASS |

Both actual axiom reports contain exactly `propext`, `Classical.choice` and
`Quot.sound`. The correct control was accepted; a changed statement, an added
axiom and `sorry` were rejected. The original FC module passed its `--wfail`
build. All required results agree with the earlier public branch run.

The fixed inputs remain FC head `7fa51437bb6717db269e4f5449b2845085c7f545`,
original proof commit `bfc411af63d0b11b2fd35d6a234249fc56080205`, Lean `v4.33.1`
and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The main integration
changed the workflow branch filter, its recorded hash and the repository README;
the mathematical inputs and verification logic were retained.

See [result.json](result.json), [comparator.log](comparator.log),
[axioms.json](axioms.json), [input receipt](before/inputs.json),
[namespace diff](before/challenge.diff), [checker environment](checker-environment.json),
[controls](controls/), and [run metadata](run.json). The artifact digest and every
evidence file hash were verified before publication. Generated evidence,
including diff context whitespace, is preserved without reformatting.

This is author-triggered reproducible CI using Lean's default kernel. It does not
claim independent third-party review or checking by a second kernel implementation.
