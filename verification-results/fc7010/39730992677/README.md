# Public verification of FC #7010

The [public CI run](https://github.com/KitaKen1/endotactic-permanence-lean/actions/runs/39730992677)
completed successfully. The executed harness commit is
[`bd6ec83aee58ba0f097611a1554b083002bebc74`](https://github.com/KitaKen1/endotactic-permanence-lean/tree/bd6ec83aee58ba0f097611a1554b083002bebc74/leanWithComparator).
This directory preserves its generated evidence. The evidence publication commit
is separate from the executed harness commit.

| Original theorem | Statement and definitions | Permitted axioms | Kernel replay |
|---|---|---|---|
| `EndotacticFC.extended_permanence` | PASS | PASS | PASS |
| `EndotacticFC.measurable_extended_permanence` | PASS | PASS | PASS |

Both original theorems use exactly `propext`, `Classical.choice` and `Quot.sound`.
The checker accepted a correct control and rejected a changed statement, an added
axiom and `sorry`. The original FC module also passed its `--wfail` build.

- FC PR head: `7fa51437bb6717db269e4f5449b2845085c7f545`.
- Original proof commit: `bfc411af63d0b11b2fd35d6a234249fc56080205`.
- Lean: `v4.33.1`; Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- Comparator: `c0c5a52d2aff92b457c3e5ed4a68c1ebc5795809`.
- lean4export: `15f6055e299ad5b89345e533cc2192f4cc00f659`.
- Landrun: `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`.

The challenge is the exact FC source with only its opening and closing namespace
declarations changed from `Endotactic` to `EndotacticFC`. The solution imports the
pinned original proof presentation without changing its sources. The checkers'
only source-tree changes are their `lean-toolchain` overrides to Lean 4.33.1.

See [result.json](result.json), [comparator.log](comparator.log),
[axioms.json](axioms.json), [input receipt](before/inputs.json),
[namespace diff](before/challenge.diff), [checker environment](checker-environment.json),
and [control logs](controls/). The downloaded workflow artifact's digest and
every file digest in `result.json` were checked before publication.

This is author-triggered reproducible CI using Lean's default kernel. It does not
claim independent third-party review or checking by a second kernel implementation.
