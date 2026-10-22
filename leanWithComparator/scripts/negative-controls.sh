#!/usr/bin/env bash
set -euo pipefail
FC_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
test "$(uname -s)" = Linux
python3 "$FC_ROOT/scripts/check-tools.py"
FC_CONTROL="$FC_ROOT/.lake/comparator-controls"
test ! -e "$FC_CONTROL"
mkdir -p "$FC_CONTROL" "$FC_ROOT/evidence/controls"
python3 - "$FC_ROOT" "$FC_CONTROL" <<'PY'
from pathlib import Path
import json,sys
root,work=map(Path,sys.argv[1:])
(work/'lean-toolchain').write_bytes((root/'lean-toolchain').read_bytes())
modules={
    'Challenge':'theorem comparatorControl : (0 : Nat) = 0 := by sorry\n',
    'Good':'theorem comparatorControl : (0 : Nat) = 0 := by rfl\n',
    'WrongStatement':'theorem comparatorControl : (1 : Nat) = 1 := by rfl\n',
    'ForbiddenAxiom':'axiom unauthorized : (0 : Nat) = 0\ntheorem comparatorControl : (0 : Nat) = 0 := unauthorized\n',
    'SorrySolution':'theorem comparatorControl : (0 : Nat) = 0 := by sorry\n',
}
(work/'lakefile.toml').write_text('name = "fc7010_comparator_controls"\n'+''.join('\n[[lean_lib]]\nname = "'+name+'"\n' for name in modules))
(work/'lake-manifest.json').write_text(json.dumps({'version':'1.2.0','packagesDir':'.lake/packages',
    'packages':[],'name':'fc7010_comparator_controls','lakeDir':'.lake','fixedToolchain':False},indent=2)+'\n')
for name,code in modules.items():(work/(name+'.lean')).write_text(code)
for name in list(modules)[1:]:
    (work/(name+'.json')).write_text(json.dumps({'challenge_module':'Challenge','solution_module':name,
        'theorem_names':['comparatorControl'],'permitted_axioms':['propext','Quot.sound','Classical.choice'],
        'enable_nanoda':False},indent=2)+'\n')
PY
bash "$FC_ROOT/scripts/sandbox-run.sh" "$FC_CONTROL" Good.json "$FC_ROOT/evidence/controls/Good.log"
grep -Fxq 'Your solution is okay!' "$FC_ROOT/evidence/controls/Good.log"
for FC_CASE in WrongStatement ForbiddenAxiom SorrySolution; do
  if bash "$FC_ROOT/scripts/sandbox-run.sh" "$FC_CONTROL" "$FC_CASE.json" "$FC_ROOT/evidence/controls/$FC_CASE.log"; then
    echo "Comparator incorrectly accepted $FC_CASE" >&2
    exit 1
  fi
done
grep -Fq 'theorem statement do not match' "$FC_ROOT/evidence/controls/WrongStatement.log"
grep -Fq "Illegal axiom detected: 'unauthorized'" "$FC_ROOT/evidence/controls/ForbiddenAxiom.log"
grep -Fq "Illegal axiom detected: 'sorryAx'" "$FC_ROOT/evidence/controls/SorrySolution.log"
printf 'PASS\n' > "$FC_ROOT/evidence/controls/status.txt"
echo 'PASS: correct proof accepted; wrong statement, extra axiom and sorry rejected'
