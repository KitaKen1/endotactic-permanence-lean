#!/usr/bin/env python3
"""Record or check metadata for the independently written FC proposal draft.

This script never writes the Lean draft. Mathematical correspondence with the
proof library is checked separately by build_audit.py.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
TARGET = ROOT / "FClikelean/EndotacticPermanence.lean"
NAMESPACE = "Endotactic"
SOURCES = {
    "Endotactic/Network.lean": [
        "Network", "Network.vector", "Network.IsEndotactic",
        "Positive", "Network.positiveClass", "Network.rhs",
    ],
    "Endotactic/Permanence.lean": [
        "AdmissibleRates", "LocallyPiecewiseDifferentiableRates",
        "Network.IsGlobalPositiveSolution", "Network.PositiveWellPosed", "Network.UniformPermanent",
        "Network.PermanentForRates",
    ],
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    text = TARGET.read_text()
    if re.findall(r"^namespace (\S+)", text, re.M) != [NAMESPACE]:
        raise ValueError("FC statements must use one mathematical namespace")
    imports = re.findall(r"^(?:public\s+)?import\s+(\S+)", text, re.M)
    if imports != ["FormalConjecturesUtil"]:
        raise ValueError(f"FC statement must import only FormalConjecturesUtil: {imports}")
    declarations = re.findall(r"^(?:def|abbrev|structure)\s+(\S+)", text, re.M)
    if declarations != [name for names in SOURCES.values() for name in names]:
        raise ValueError("Update the mathematical correspondence map for changed FC declarations")
    start = text.index("namespace " + NAMESPACE + "\n") + len("namespace " + NAMESPACE + "\n")
    theorem = text.index("theorem extended_permanence")
    end = text.rfind("/--", start, theorem)
    if end < start:
        raise ValueError("Missing conjecture docstring")
    metadata = {
        "metadata_script": "lean/scripts/make_fc_support.py",
        "lean_draft_is_independent_source": True,
        "single_file": True,
        "statement": "FClikelean/EndotacticPermanence.lean",
        "imports": imports, "namespace": NAMESPACE, "single_namespace": True,
        "definition_bodies_preserved_modulo_type_aliases": False,
        "expanded_type_aliases": {
            "Endotactic.State": "Fin d → ℝ", "Endotactic.Complex": "Fin d → ℕ",
        },
        "presentation_changes": {
            "Endotactic.Network": "Uses Fin m reaction indices instead of an arbitrary finite type.",
            "Endotactic.dot": "Uses mathlib dotProduct directly.",
            "Endotactic.realComplex": "Casts coefficients to real numbers directly.",
            "Endotactic.Network.PermanentForRates":
                "Uses positive coordinate bounds. Equivalence with compact absorption is proved in Lean.",
            "Endotactic.Network.UniformPermanent":
                "Uses common positive coordinate bounds for all measurable rate paths. "
                "Equivalence with common compact absorption is proved in Lean.",
        },
        "inlined_definitions": [
            "Endotactic.Network.projection", "Endotactic.Network.sourceLevel",
            "Endotactic.monomial", "Endotactic.Network.stoichiometricSubspace",
            "Endotactic.Network.IsIntegralSolution", "Endotactic.EventuallyIn",
        ],
        "excluded_unused_definitions": [
            "Endotactic.ExtendedPermanenceConjecture",
            "Endotactic.MeasurableExtendedPermanenceConjecture",
            "Endotactic.OriginalExtendedPermanenceConjecture",
        ],
        "sources": {
            name: {
                "original_sha256": sha((ROOT / "lean" / name).read_bytes()),
                "declarations": [NAMESPACE + "." + n for n in names],
            }
            for name, names in SOURCES.items()
        },
        "definitions_sha256": sha(text[start:end].strip().encode()),
        "definition_count": len(declarations),
        "def_count": len(re.findall(r"^def\s+", text, re.M)),
        "structure_count": len(re.findall(r"^structure\s+", text, re.M)),
        "finite_reaction_indices": True,
        "permanence_presentation": "eventual positive coordinate bounds",
        "proof_presentation": "lean/EndotacticPublication/FCPresentation.lean",
        "compact_equivalence": "lean/EndotacticPublication/CoordinateBounds.lean",
    }
    mapping = ROOT / "FClikelean/source-map.json"
    if args.check:
        if json.loads(mapping.read_text()) != metadata:
            raise ValueError("Stale FC draft metadata; run make_fc_support.py to record it")
    else:
        mapping.write_text(json.dumps(metadata, indent=2) + "\n")
    print(f"FC proposal draft: {len(declarations)} definitions; independently written single file")


if __name__ == "__main__":
    main()
