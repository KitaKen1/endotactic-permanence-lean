# FC #7010 verification records

| Run | Branch | Result | Preserved evidence |
|---|---|---|---|
| [39740750951](https://github.com/KitaKen1/endotactic-permanence-lean/actions/runs/39740750951) | `main` | PASS | [main verification](39740750951/) |
| [39730992677](https://github.com/KitaKen1/endotactic-permanence-lean/actions/runs/39730992677) | `fc7010-endotactic-comparator-20261022` | PASS | [earlier public verification](39730992677/) |

Both runs compare the two original pinned proofs with the same FC revision,
restrict their axioms, and replay the solution through Lean's kernel. Each record
identifies its executed harness commit separately from the commit publishing the
evidence. The [current harness](../../leanWithComparator/) is available on main.
