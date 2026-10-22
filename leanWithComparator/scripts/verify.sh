#!/usr/bin/env bash
set -euo pipefail
FC_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
test "$(uname -s)" = Linux
cd "$FC_ROOT"
mkdir -p evidence
printf 'NOT_RUN\n' > evidence/status.txt
trap 'code=$?; if [[ $code -ne 0 ]]; then printf "FAIL: exit=%s\n" "$code" > evidence/status.txt; fi' EXIT
python3 scripts/check-inputs.py --require-dependencies --receipt-dir evidence/before
python3 scripts/check-tools.py
test "$(cat evidence/controls/status.txt)" = PASS
{
  date -u +started_utc=%FT%TZ
  uname -a
  id
  lake env lean --version
  printf 'harness_commit=%s\n' "$(git rev-parse HEAD)"
  printf 'run=%s/%s/actions/runs/%s\n' "${GITHUB_SERVER_URL:-https://github.com}" "${GITHUB_REPOSITORY:-local}" "${GITHUB_RUN_ID:-local}"
} > evidence/environment.txt
# This is the first step that elaborates or imports the original solution.
# Comparator builds and exports Challenge before Solution, under real Landrun.
bash scripts/sandbox-run.sh "$FC_ROOT" comparator.json "$FC_ROOT/evidence/comparator.log"
grep -Fxq 'Lean default kernel accepts the solution' evidence/comparator.log
grep -Fxq 'Your solution is okay!' evidence/comparator.log
python3 scripts/check-inputs.py --require-dependencies --receipt-dir evidence/after-comparator
lake env lean -DwarningAsError=true Audit.lean 2>&1 | tee evidence/axioms.log
python3 scripts/check-axioms.py evidence/axioms.log evidence/axioms.json
# Also check the unmodified actual PR module with its own FC library options.
lake --wfail build 'FormalConjectures.Arxiv.«1010.3050».EndotacticPermanence' \
  2>&1 | tee evidence/fc-module-build.log
python3 scripts/check-inputs.py --require-dependencies --receipt-dir evidence/after
python3 - <<'PY'
from pathlib import Path
import datetime,hashlib,json,os,subprocess
root=Path.cwd();out=root/'evidence';pins=json.loads((root/'pins.json').read_text())
axioms=json.loads((out/'axioms.json').read_text())['targets']
record={
    'status':'PASS','checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'harness_commit':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
    'fc_head':pins['pr_head'],'proof_commit':pins['proof_commit'],
    'run_url':f"https://github.com/{os.environ.get('GITHUB_REPOSITORY','local')}/actions/runs/{os.environ.get('GITHUB_RUN_ID','local')}",
    'lean_toolchain':pins['lean_toolchain'],
    'targets':{name:{'statement_and_definitions':True,'axioms':axioms[name],
                     'permitted_axioms_only':True,'kernel_replay':True} for name in pins['targets']},
    'comparator':True,'axiom_audit':True,'fc_module_build':True,'negative_controls':True,
    'kernel':'Lean default kernel, v4.33.1',
    'independent_kernel_implementation':False,'independent_third_party_review':False,
    'evidence_sha256':{str(p.relative_to(out)):hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(out.rglob('*')) if p.is_file() and p.name not in ['status.txt','result.json']}}
(out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
summary=os.environ.get('GITHUB_STEP_SUMMARY')
if summary:
    with open(summary,'a') as f:
        f.write('## FC #7010 verification: PASS\n\n')
        f.write('| Original theorem | Statement / definitions | Axioms | Kernel replay |\n|---|---|---|---|\n')
        for name in pins['targets']:
            f.write(f"| `{name}` | PASS | `{', '.join(axioms[name])}` | PASS |\n")
        f.write('\nAuthor-triggered CI. Fixed inputs and full evidence are in the workflow artifact.\n')
PY
printf 'PASS\n' > evidence/status.txt
echo 'PASS: both pinned proofs compared, axiom-audited and replayed through the Lean kernel'
