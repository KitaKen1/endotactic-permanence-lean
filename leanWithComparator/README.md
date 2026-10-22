# FC #7010: fixed-commit verification

This harness compares both external endotactic permanence proofs with the exact
Formal Conjectures PR #7010 statement. It checks statement and definition
correspondence, restricts proof axioms to `propext`, `Classical.choice` and
`Quot.sound`, and replays the exported proof environment through Lean's kernel.

Inputs are pinned in `pins.json`: FC head
`7fa51437bb6717db269e4f5449b2845085c7f545`, proof commit
`bfc411af63d0b11b2fd35d6a234249fc56080205`, and Lean `v4.33.1`.
`Challenge.lean` is the byte-for-byte PR source except for its opening and closing
namespace declarations (`Endotactic` becomes `EndotacticFC`). `Solution.lean`
imports the original proof presentation without changing its sources. The
environments remain separate, and the solution never imports the challenge.

## Reproduce

Use a disposable Linux VM with Landlock and systemd, an unprivileged user with
sudo for the restricted systemd service, Git, Go, Python 3, and Elan. The checker
and exporter are compiled with Lean 4.33.1; their only upstream file changes are
the recorded `lean-toolchain` overrides. Checker source files remain unchanged.
The legacy checker is pinned to retain the original proof environment; new Lean
versions also provide integrated `lake comparator` and `lake check` commands.

From the repository root:

```bash
export COMPARATOR_TOOLS="$(mktemp -d)"
(cd leanWithComparator && lake exe cache get)
python3 leanWithComparator/scripts/check-inputs.py --require-dependencies
bash leanWithComparator/scripts/install-tools.sh
bash leanWithComparator/scripts/negative-controls.sh
bash leanWithComparator/scripts/verify.sh
```

The first compilation of the solution occurs inside Comparator's real Landrun
sandbox, after building/exporting the trusted challenge. The systemd service
disallows AF_UNIX sockets and runs as the invoking unprivileged user. No fake
sandbox is used. Mathlib dependency caches are trusted and permitted; original
project proof artifacts and earlier audit results are not restored.

The normal control must pass. Wrong statements, an extra mathematical axiom, and
`sorry` must each fail for the expected reason. The original FC module is also
built with `--wfail`. Any failed command or missing target result fails the run.

Full success or failure logs, tool source and binary hashes, input receipts,
namespace diff, actual per-theorem axiom reports, and `result.json` are uploaded
as workflow evidence for 90 days. `result.json` is only produced after every
required check passes. Its `harness_commit` is the commit actually executed.

This is author-triggered CI, not independent third-party review. It uses Lean's
default kernel, not a second independent kernel implementation. Do not report a
successful verification until the full workflow finishes with `PASS`.
