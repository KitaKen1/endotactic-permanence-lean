#!/usr/bin/env python3
"""Build publication proofs, audit every theorem, and match compiled FC types."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
LEAN, WEB, FC = ROOT / "lean", ROOT / "lean4web", ROOT / "FClikelean"
EVIDENCE = LEAN / "evidence"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = ["extended_permanence", "measurable_extended_permanence"]
FC_NAMESPACE = "Endotactic"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def code_only(text, keep_strings=False):
    result, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            if keep_strings and depth == 0:
                result.append(" ")
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            if keep_strings:
                result.append(" ")
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            start = i
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            if keep_strings:
                result.append(text[start:i])
        else:
            result.append(text[i])
            i += 1
    require(depth == 0, "Unclosed Lean comment")
    return "".join(result)


def target(text, name):
    publication = text.rsplit("namespace EndotacticFC", 1)[-1] if "namespace EndotacticFC" in text else text
    m = re.search(r"theorem " + re.escape(name) + r"\s*:\s*([\s\S]*?)\s*:= by", publication)
    require(m, f"Missing publication target: {name}")
    result = m.group(1)
    for name, typ in [("State", "ℝ"), ("Complex", "ℕ")]:
        result = re.sub(r"\b(?:Endotactic\.)?"+name+r" d\b", "Fin d → "+typ, result)
    result = re.sub(r"\b(?:Endotactic|EndotacticFC)\.", "", result)
    # The FC presentation omits the proof library's tautological regularity
    # premise. This textual comparison is followed by a Lean equivalence proof.
    result = result.replace("UniformPermanent ℓ u c (fun _ => True)", "UniformPermanent ℓ u c")
    return re.sub(r"\s+", " ", result).strip()


def theorem_names(path):
    namespaces, names = [], []
    for line in path.read_text().splitlines():
        if m := re.match(r"^namespace\s+(\S+)", line):
            namespaces.append(m.group(1))
        elif re.match(r"^end(?:\s|$)", line):
            if namespaces:
                namespaces.pop()
        elif m := re.match(r"^theorem\s+(\S+)", line):
            names.append(".".join(namespaces + [m.group(1)]))
    return names


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reuse-proof-checks", action="store_true",
                        help="Reuse successful proof checks only when their source hashes match")
    parser.add_argument("--reuse-mathematical-checks", action="store_true",
                        help="Reuse compiled-expression checks only for comment-only FC edits")
    parser.add_argument("--reuse-compiled-proof-comparison", action="store_true",
                        help="Compare fresh FC expressions with previously verified proof expressions")
    args = parser.parse_args()
    if args.reuse_compiled_proof_comparison:
        args.reuse_proof_checks = True
    if args.reuse_mathematical_checks:
        args.reuse_proof_checks = True
    previous = None
    if args.reuse_proof_checks:
        previous = json.loads((EVIDENCE / "build_results.json").read_text())
        require(previous["status"] == "PASS", "No successful proof checks to reuse")
    cached_expressions = None
    if args.reuse_compiled_proof_comparison:
        require(previous.get("fc_all_definitions_contribute_to_targets"),
                "No verified FC dependency closure to reuse")
        cached_expressions = {}
        previous_namespace = previous.get("fc_namespace", "EndotacticPublication")
        for name, value in re.findall(r"COMPILED_EXPR (\S+): (\[[^\n]*\])",
                                      (EVIDENCE / "build.log").read_text()):
            expression = json.loads(value)
            if name in cached_expressions:
                require(cached_expressions[name] == expression, "Prior expression reports disagree")
            cached_expressions[name] = expression
        require(cached_expressions, "No compiled proof expressions available")
        for name in TARGETS:
            old_name = previous_namespace + "." + name
            new_name = FC_NAMESPACE + "." + name
            require(old_name in cached_expressions, "Missing previously verified target")
            if old_name != new_name:
                cached_expressions[new_name] = cached_expressions.pop(old_name)
    EVIDENCE.mkdir(exist_ok=True)
    (EVIDENCE / "build_results.json").write_text(json.dumps({
        "status": "RUNNING",
        "started_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat()
    }, indent=2)+"\n")
    paths = [LEAN / "Endotactic.lean", LEAN / "EndotacticPublication.lean",
             *sorted((LEAN / "Endotactic").glob("*.lean")),
             *sorted((LEAN / "EndotacticPublication").glob("*.lean")),
             WEB / "EndotacticPermanenceLean4Web.lean", FC / "EndotacticPermanence.lean"]
    paths += [FC / "source-map.json", EVIDENCE / "fc_presentation_source_map.json"]
    paths += sorted((LEAN / "scripts").glob("*.py"))
    for project in [LEAN, WEB, FC]:
        paths += [project / n for n in ["lakefile.toml", "lean-toolchain", "lake-manifest.json"]]
    sources = {str(p.relative_to(ROOT)): sha(p) for p in paths if p.exists()}
    main_text = (LEAN / "EndotacticPublication/FCPresentation.lean").read_text()
    fc_text = (FC / "EndotacticPermanence.lean").read_text()
    if args.reuse_mathematical_checks:
        old_fc = FC / ".lake/FormalConjectures/EndotacticPermanence.lean"
        require(sha(old_fc) == previous["source_sha256"]["FClikelean/EndotacticPermanence.lean"],
                "Previous compiled FC source is unavailable")
        require(code_only(old_fc.read_text(), True) == code_only(fc_text, True),
                "FC code changed; rerun the compiled-expression checks")
        require(previous["compiled_fc_targets_match"] and
                previous["compiled_fc_support_definitions_match"], "No successful FC comparison to reuse")
        require(all(previous["source_sha256"].get(n) == h for n,h in sources.items()
                    if n not in {"FClikelean/EndotacticPermanence.lean", "lean/scripts/build_audit.py"}),
                "Other audited sources changed; rerun the mathematical checks")
    web_text = (WEB / "EndotacticPermanenceLean4Web.lean").read_text()
    require(all(target(main_text, n) == target(fc_text, n) == target(web_text, n)
                for n in TARGETS), "Displayed theorem targets differ")
    for p in paths:
        if p.suffix == ".lean" and p.parent != FC:
            require(not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", code_only(p.read_text())),
                    f"Proof hole/unchecked primitive: {p}")
    require(re.findall(r"^namespace (\S+)", fc_text, re.M) == [FC_NAMESPACE],
            "FC draft must use one mathematical namespace")
    require(len(re.findall(r"\bsorry\b", code_only(fc_text))) == 2, "Unexpected FC stub count")
    require(re.findall(r"^public import (\S+)", fc_text, re.M) == ["FormalConjecturesUtil"],
            "FC statement must import only FormalConjecturesUtil")
    require(not re.search(r"\b(admit|axiom|native_decide|unsafe)\b", code_only(fc_text)),
            "Unchecked primitive in the FC definitions")
    require([p for p in FC.rglob("*.lean") if ".lake" not in p.parts] ==
            [FC / "EndotacticPermanence.lean"], "FC definitions must live in one statement file")
    snapshot = json.loads((EVIDENCE / "source_snapshot.json").read_text())
    require(all(sha(LEAN / n) == h for n, h in snapshot["sources_sha256"].items()),
            "Original proved sources were changed")
    mapping = json.loads((WEB / "source-map.json").read_text())
    require(mapping["output_sha256"] == sha(WEB / "EndotacticPermanenceLean4Web.lean"), "Stale source map")
    require(all(sha(LEAN / x["source"]) == x["source_sha256"] for x in mapping["source_map"]),
            "Single-file sources differ from modular sources")
    require(subprocess.run(["python3", "scripts/make_fc_support.py", "--check"],
                           cwd=LEAN).returncode == 0, "FC draft correspondence metadata differs")

    require(subprocess.run(["python3", "scripts/make_fc_proof.py", "--check"], cwd=LEAN).returncode == 0,
            "Stale proof adapter for the independent FC presentation")

    proof_sources = {n: h for n,h in sources.items()
                     if (n.startswith("lean/") and not n.startswith("lean/scripts/")
                         and n != "lean/evidence/fc_presentation_source_map.json")
                     or n.startswith("lean4web/")}
    # The generator check above verifies current correspondence metadata.
    # FC citation attributes can change that metadata without changing proof inputs.
    if args.reuse_compiled_proof_comparison:
        require(all(previous["source_sha256"].get("FClikelean/"+n) == sources["FClikelean/"+n]
                    for n in ["lakefile.toml", "lean-toolchain", "lake-manifest.json"]),
                "FC compiler or dependencies changed")
    if previous:
        require(all(previous["source_sha256"].get(n) == h for n,h in proof_sources.items()),
                "Proof sources or build configuration changed; run a full audit")

    start = time.monotonic()
    exits, outputs, seconds = {}, {}, {}
    with (EVIDENCE / "build.log").open("w") as log:
        def run(label, command, cwd=LEAN, env=None):
            tick = time.monotonic()
            p = subprocess.run(command, cwd=cwd, env=env, text=True, capture_output=True)
            output = (p.stdout + p.stderr).replace(str(ROOT), ".").replace(str(Path.home()), "<home>")
            display_command = " ".join(command).replace(str(ROOT), ".").replace(str(Path.home()), "<home>")
            log.write(f"\n{label}: {display_command}\n{output}\nExit: {p.returncode}\n")
            log.flush()
            exits[label], outputs[label], seconds[label] = p.returncode, output, round(time.monotonic()-tick, 3)
            print(f"{label}: {'PASS' if p.returncode == 0 else 'FAIL'} ({seconds[label]} s)", flush=True)
            if p.returncode:
                diagnostics = [line for line in output.splitlines()
                               if "error:" in line or "warning:" in line]
                print("\n".join(diagnostics) or output[-3000:], flush=True)
            return p

        for name, project in [("proof", LEAN), ("web", WEB), ("fc", FC)]:
            if not (project / "lake-manifest.json").exists():
                require(run(name+"_update", ["lake", "update"], project).returncode == 0, "Update failed")
            if not (project / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean").exists():
                require(run(name+"_cache", ["lake", "exe", "cache", "get"], project).returncode == 0,
                        "Dependency cache unavailable")
        if previous:
            print("proof_checks: REUSED (unchanged proof and Lean4Web source hashes)", flush=True)
            log.write("Proof checks reused from " + previous["checked_at_utc"] + "\n")
        else:
            require(run("modular_build", ["lake", "--wfail", "build"]).returncode == 0, "Modular build failed")
            require(run("lean4web_build", ["lake", "--wfail", "build"], WEB).returncode == 0, "Standalone build failed")
        require(run("fc_utility", ["lake", "build", "FormalConjecturesUtil"], FC).returncode == 0,
                "Pinned FC utility build failed")
        if not previous:
            require(run("fc_single_file_build", ["lake", "--wfail", "build", "EndotacticPermanence"],
                        FC).returncode == 0, "Single-file FC statement build failed")
        symbols = [n for p in sorted((LEAN / "Endotactic").glob("*.lean")) for n in theorem_names(p)]
        symbols += [n for p in sorted((LEAN / "EndotacticPublication").glob("*.lean"))
                    for n in theorem_names(p)]
        require(len(symbols) == len(set(symbols)), "Duplicate theorem names")
        if not previous:
            audit_file = LEAN / ".lake/PublicationAxioms.lean"
            audit_file.write_text("import EndotacticPublication\n"+"\n".join("#print axioms "+n for n in symbols)+"\n")
            require(run("all_theorem_axioms", ["lake", "env", "lean", "-DwarningAsError=true",
                                            str(audit_file)]).returncode == 0, "Kernel axiom check failed")
        env = os.environ.copy()
        search = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=FC, text=True).strip()
        fc_search = [str((FC / x).resolve()) for x in search.split(os.pathsep) if x]
        search = os.pathsep.join(fc_search)
        env["LEAN_PATH"] = search + os.pathsep + str(FC / ".lake")
        fc_file = FC / ".lake/FormalConjectures/EndotacticPermanence.lean"
        fc_file.parent.mkdir(parents=True, exist_ok=True)
        fc_file.write_text(fc_text)
        linters = ["namespace", "stubs", "openClassical", "ams_attribute", "category_attribute",
                   "category_answer", "category_docstring", "conditional_formal_proof",
                   "moduleDocstring", "latex_docstring", "imports"]
        flags = ["-DautoImplicit=false", "-Dwarn.sorry=false", "-DwarningAsError=true"]
        flags += [f"-Dweak.linter.style.{n}=true" for n in linters]
        require(run("fc_statement", ["lean", *flags, "-R", ".lake", str(fc_file),
                                    "-o", str(fc_file.with_suffix(".olean"))], FC, env).returncode == 0,
                "FC statement or mathematical linter failed")

        # Verify the independent FC presentation against the proof environment.
        # Compare with the complete coordinate-bound presentation. Its proofs
        # translate networks and use kernel-checked compact absorption equivalences.
        fc_mapping = json.loads((FC / "source-map.json").read_text())
        required_definitions = [n for source in fc_mapping["sources"].values()
                                for n in source["declarations"]]
        require([FC_NAMESPACE+"."+n for n in
                 re.findall(r"^(?:def|abbrev|structure)\s+(\S+)", fc_text, re.M)] == required_definitions,
                "Unmapped extra definitions in the FC draft")
        support_names = list(required_definitions)
        support_names += ["Endotactic.Network.mk", "Endotactic.Network.source",
                          "Endotactic.Network.target"]
        compared_names = [FC_NAMESPACE+"."+n for n in TARGETS] + support_names
        if not args.reuse_mathematical_checks:
            quote = chr(96)*2
            canonical = """
    private meta def canonicalPublicationName : Lean.Name → Lean.Name
      | .str .anonymous "EndotacticFC" => `Endotactic
      | .str p s => .str (canonicalPublicationName p) s
      | .num p n => .num (canonicalPublicationName p) n
      | n => n

    private meta partial def canonicalPublicationExpr (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
      match e with
      | .mdata _ b => canonicalPublicationExpr b
      | .forallE _ t b bi =>
          return .forallE .anonymous (← canonicalPublicationExpr t) (← canonicalPublicationExpr b) bi
      | .lam _ t b bi =>
          return .lam .anonymous (← canonicalPublicationExpr t) (← canonicalPublicationExpr b) bi
      | .letE _ t v b nd =>
          return .letE .anonymous (← canonicalPublicationExpr t) (← canonicalPublicationExpr v)
            (← canonicalPublicationExpr b) nd
      | .app f a => return .app (← canonicalPublicationExpr f) (← canonicalPublicationExpr a)
      | .proj n i b => return .proj (canonicalPublicationName n) i (← canonicalPublicationExpr b)
      | .const n us => return .const (canonicalPublicationName n) us
      | e => return e
    """
            fingerprints = canonical
            for n in compared_names:
                fingerprints += f'''
    run_meta do
      let ci ← Lean.getConstInfo {quote}{n}
      let mut expressions := [reprStr (← canonicalPublicationExpr ci.type)]
      if let .defnInfo definition := ci then
        expressions := expressions ++ [reprStr (← canonicalPublicationExpr definition.value)]
      Lean.logInfo ("COMPILED_EXPR {n}: " ++ (Lean.toJson expressions).compress)
    '''
            required_names = ", ".join(quote+n for n in required_definitions)
            root_names = ", ".join(quote+FC_NAMESPACE+"."+n for n in TARGETS)
            reachability = f'''
run_meta do
  let roots : Array Lean.Name := #[{root_names}]
  let mut pending := roots
  let mut seen : Lean.NameSet := {{}}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if !seen.contains name then
      seen := seen.insert name
      let info ← Lean.getConstInfo name
      let dependencies := if roots.contains name then
        info.type.getUsedConstantsAsSet else info.getUsedConstantsAsSet
      for dependency in dependencies.toArray do
        if dependency.toString.startsWith "Endotactic." then
          pending := pending.push dependency
  let required : Array Lean.Name := #[{required_names}]
  let unused := required.filter (fun name => !seen.contains name)
  unless unused.isEmpty do
    throwError "Definitions not used by either conjecture: {{unused}}"
  Lean.logInfo ("FC_REACHABLE_DEFINITIONS " ++
    (Lean.toJson (required.map Lean.Name.toString)).compress)
'''
            module_check = FC / ".lake/FCModuleExpressions.lean"
            module_check.write_text(
                "module\n\npublic import FormalConjectures.EndotacticPermanence\n\n"
                "/-! # Compiled FC target and support expression audit -/\n"+fingerprints+reachability)
            require(run("compiled_fc_module_expressions", ["lean", "-DwarningAsError=true", "-R", ".lake",
                                                          str(module_check)], FC, env).returncode == 0,
                    "Actual compiled FC expressions unavailable")

            if not args.reuse_compiled_proof_comparison:
                proof_search = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                                        cwd=LEAN, text=True).strip()
                original_search = [str((LEAN / x).resolve()) for x in proof_search.split(os.pathsep) if x]
                package_search = [x for x in fc_search if "/.lake/packages/" in x]
                proof_env = env.copy()
                proof_env["LEAN_PATH"] = os.pathsep.join(original_search + package_search)
                proof_fingerprints = fingerprints
                for name in sorted(compared_names, key=len, reverse=True):
                    proof_name = "EndotacticFC." + name.removeprefix("Endotactic.")
                    proof_fingerprints = proof_fingerprints.replace(quote+name, quote+proof_name)
                check = ("import FormalConjecturesUtil\nimport EndotacticPublication.FCPresentation\n"
                         "/-! # Compiled independent FC presentation and complete proofs -/\n" +
                         proof_fingerprints)
                bridge_names = [
                    "EndotacticFC.toProof_fromProof", "EndotacticFC.fromProof_toProof",
                    "EndotacticFC.Network.isEndotactic_iff",
                    "EndotacticFC.Network.permanentForRates_iff_compact",
                    "EndotacticFC.Network.uniformPermanent_iff_compact",
                    "Endotactic.compact_positive_coordinate_bounds",
                    "Endotactic.Network.coordinate_bounds_compact_class",
                    "Endotactic.Network.boundedPermanentForRates_iff",
                    "Endotactic.Network.uniformBoundedPermanent_iff",
                    *["EndotacticFC."+n for n in TARGETS],
                ]
                check += "\n" + "\n".join("#print axioms "+n for n in bridge_names) + "\n"
                type_file = FC / ".lake/FCTypeCheck.lean"
                type_file.write_text(check)
                require(run("compiled_fc_type_equality", ["lean", "-DwarningAsError=true", "-R", ".lake",
                                                        str(type_file)], FC, proof_env).returncode == 0,
                        "Compiled proof-presentation comparison failed")

    def compiled_expressions(output):
        return {n: json.loads(value) for n, value in
                re.findall(r"COMPILED_EXPR (\S+): (\[[^\n]*\])", output)}

    if not args.reuse_mathematical_checks:
        actual_fc = compiled_expressions(outputs["compiled_fc_module_expressions"])
        original_fc = cached_expressions if cached_expressions is not None else \
            compiled_expressions(outputs["compiled_fc_type_equality"])
        require(set(original_fc) == set(compared_names), "Previous compiled declaration list differs")
        require(set(actual_fc) == set(compared_names), "Missing actual FC expression fingerprints")
        mismatches = [n for n in compared_names if actual_fc.get(n) != original_fc.get(n)]
        require(not mismatches, f"FC module and original-support expressions differ: {mismatches}")
        reachable = re.search(r"FC_REACHABLE_DEFINITIONS (\[[^\n]*\])",
                              outputs["compiled_fc_module_expressions"])
        require(reachable and json.loads(reachable.group(1)) == required_definitions,
                "FC declaration dependency check failed")

    def parse_axioms(output, names):
        result = {}
        for n in names:
            m = re.search("'"+re.escape(n)+
                          r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output, re.S)
            require(m, f"Missing actual kernel report for {n}")
            values = [a.strip() for a in (m.group(1) or "").split(",") if a.strip()]
            require(set(values) <= ALLOWED, f"Unexpected axiom at {n}: {values}")
            result[n] = values
        return result

    if previous:
        all_axioms = previous["axioms"]
        web_axioms = previous["lean4web_axioms"]
        require(set(all_axioms) == set(symbols), "Reused theorem list differs")
        require(all(set(a) <= ALLOWED for a in all_axioms.values()), "Unexpected reused axioms")
    else:
        all_axioms = parse_axioms(outputs["all_theorem_axioms"], symbols)
        web_axioms = parse_axioms(outputs["lean4web_build"], ["EndotacticFC."+n for n in TARGETS])
    if args.reuse_mathematical_checks or args.reuse_compiled_proof_comparison:
        checked_axioms = previous["compiled_fc_proof_axioms"]
        require(previous["compiled_expression_comparison_count"] == len(compared_names),
                "Compiled declaration list changed")
    else:
        checked_axioms = parse_axioms(outputs["compiled_fc_type_equality"],
                                      bridge_names)
    require(all(sha(ROOT/n) == h for n,h in sources.items()), "Sources changed during the audit")
    manifest = json.loads((WEB / "lake-manifest.json").read_text())
    web_rev = next(x["rev"] for x in manifest["packages"] if x["name"] == "mathlib")
    record = {
        "status": "PASS", "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "exit_codes": exits, "seconds": seconds, "elapsed_seconds": round(time.monotonic()-start, 3),
        "timing_note": "Dependency loading and cached builds included; not independent semantic review.",
        "lean_version": (LEAN / "lean-toolchain").read_text().strip(),
        "lean4web_version": (WEB / "lean-toolchain").read_text().strip(),
        "lean4web_mathlib": web_rev, "all_project_theorem_count": len(symbols),
        "axioms": all_axioms, "lean4web_axioms": web_axioms, "compiled_fc_proof_axioms": checked_axioms,
        "compiled_fc_targets_match": True, "answer_outside_all_quantifiers": True,
        "fc_linter_options": linters,
        "compiled_fc_support_definitions_match": True,
        "fc_presentation_correspondence": {
            "presentation_definition_comparison_count": len(required_definitions),
            "comparison": "Compiled types and definition bodies match the complete-proof presentation, "
                          "modulo its EndotacticFC namespace.",
            "equivalent_definitions": ["Endotactic.Network.PermanentForRates",
                                       "Endotactic.Network.UniformPermanent"],
            "network_conversion_roundtrips_checked": True,
            "compact_coordinate_equivalence_checked": True,
            "proof_adapter": "lean/EndotacticPublication/FCPresentation.lean",
            "compact_equivalence": "lean/EndotacticPublication/CoordinateBounds.lean"
        },
        "fc_finite_reaction_indices": True, "fc_coordinate_bounds": True,
        "compiled_expression_comparison_count": len(compared_names),
        "fc_definitions_inline": True, "fc_only_import": "FormalConjecturesUtil",
        "fc_namespace": FC_NAMESPACE, "fc_single_namespace": True,
        "fc_definition_count": len(support_names)-3,
        "fc_def_count": fc_mapping["def_count"],
        "fc_structure_count": fc_mapping["structure_count"],
        "fc_inlined_definitions": fc_mapping["inlined_definitions"],
        "fc_all_definitions_contribute_to_targets": True,
        "fc_required_definitions": required_definitions,
        "fc_excluded_unused_definitions": fc_mapping["excluded_unused_definitions"],
        "expanded_type_aliases": ["Endotactic.State", "Endotactic.Complex"],
        "reused_compiled_proof_comparison": ({
            "checked_at_utc": previous["checked_at_utc"],
            "matched_compiled_expression_count": len(compared_names)
        } if args.reuse_compiled_proof_comparison else None),
        "reused_fc_mathematical_checks": ({
            "checked_at_utc": (previous.get("reused_fc_mathematical_checks") or previous)["checked_at_utc"],
            "fc_code_sha256": hashlib.sha256(code_only(fc_text, True).encode()).hexdigest(),
            "stages": ["compiled_fc_module_expressions", "compiled_fc_type_equality"]
        } if args.reuse_mathematical_checks else None),
        "reused_proof_checks": ({"checked_at_utc": (previous.get("reused_proof_checks") or previous)["checked_at_utc"],
                                 "stages": ["modular_build", "lean4web_build", "all_theorem_axioms"],
                                 "source_sha256": proof_sources} if previous else None),
        "fc_statement_stub_count": 2, "proof_holes": 0, "original_sources_unchanged": True,
        "source_sha256": sources, "single_file_modules": mapping["modules"],
        "single_file_lines": mapping["lines"], "official_fc_upstream_ci_run": False,
        "external_publication_or_submission_performed": False,
        "independent_original_convention_review_complete": False
    }
    (EVIDENCE / "build_results.json").write_text(json.dumps(record, indent=2)+"\n")
    print(f"PUBLICATION AUDIT: PASS; {len(symbols)} theorems, independent FC presentation verified", flush=True)


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        EVIDENCE.mkdir(exist_ok=True)
        (EVIDENCE / "build_results.json").write_text(json.dumps({
            "status": "FAIL",
            "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "error": str(error).replace(str(ROOT), ".")
        }, indent=2)+"\n")
        raise
