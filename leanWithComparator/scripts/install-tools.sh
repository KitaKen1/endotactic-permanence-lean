#!/usr/bin/env bash
set -euo pipefail
FC_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
: "${COMPARATOR_TOOLS:?Set COMPARATOR_TOOLS to a fresh absolute directory}"
test "$(uname -s)" = Linux
test "${COMPARATOR_TOOLS:0:1}" = /
mkdir -p "$COMPARATOR_TOOLS/bin"
export PATH="$HOME/.elan/bin:$PATH"
read -r FC_CMP FC_EXPORT FC_LANDRUN < <(python3 - "$FC_ROOT/pins.json" <<'PY'
import json,sys
p=json.load(open(sys.argv[1]));print(p['comparator_commit'],p['lean4export_commit'],p['landrun_commit'])
PY
)
git clone --quiet https://github.com/zouuup/landrun.git "$COMPARATOR_TOOLS/landrun"
git -C "$COMPARATOR_TOOLS/landrun" checkout --quiet --detach "$FC_LANDRUN"
(cd "$COMPARATOR_TOOLS/landrun" && go build -trimpath -o "$COMPARATOR_TOOLS/bin/landrun" ./cmd/landrun)
git clone --quiet https://github.com/leanprover/comparator.git "$COMPARATOR_TOOLS/comparator"
git -C "$COMPARATOR_TOOLS/comparator" checkout --quiet --detach "$FC_CMP"
git clone --quiet https://github.com/leanprover/lean4export.git "$COMPARATOR_TOOLS/lean4export"
git -C "$COMPARATOR_TOOLS/lean4export" checkout --quiet --detach "$FC_EXPORT"
python3 - "$FC_ROOT/pins.json" "$COMPARATOR_TOOLS" <<'PY'
from pathlib import Path
import json,sys
p=json.load(open(sys.argv[1]));root=Path(sys.argv[2])
for name in ['comparator','lean4export']:
    file=root/name/'lean-toolchain'
    assert file.read_text().strip()==p['tools_upstream_toolchain'], 'Unexpected upstream toolchain'
    file.write_text(p['lean_toolchain']+'\n')
PY
(cd "$COMPARATOR_TOOLS/comparator" && lake build comparator)
test "$(git -C "$COMPARATOR_TOOLS/comparator/.lake/packages/lean4export" rev-parse HEAD)" = "$FC_EXPORT"
(cd "$COMPARATOR_TOOLS/lean4export" && lake build lean4export)
python3 "$FC_ROOT/scripts/check-tools.py"
