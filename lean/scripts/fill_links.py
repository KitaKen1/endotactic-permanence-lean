#!/usr/bin/env python3
"""Verify a real published commit, then fill local proof and Lean4Web links."""
import argparse
import hashlib
import json
from pathlib import Path
import re
from urllib.parse import quote, urlparse
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repository", help="Existing https://github.com/OWNER/REPO")
    parser.add_argument("commit", help="Public full 40-character source commit")
    parser.add_argument("--dry-run", action="store_true", help="Verify and print links without editing")
    args = parser.parse_args()
    url = urlparse(args.repository.rstrip("/"))
    if (url.scheme != "https" or url.netloc != "github.com" or url.query or url.fragment or
            not re.fullmatch(r"/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", url.path)):
        parser.error("Use a plain HTTPS GitHub repository URL")
    if not re.fullmatch(r"[0-9a-fA-F]{40}", args.commit):
        parser.error("Use a full 40-character commit SHA")
    repo, revision = args.repository.rstrip("/"), args.commit.lower()
    files = ["lean/EndotacticPublication/FCPresentation.lean", "lean4web/EndotacticPermanenceLean4Web.lean"]
    for name in files:
        raw = f"https://raw.githubusercontent.com{url.path}/{revision}/{name}"
        with urlopen(Request(raw, headers={"User-Agent": "EndotacticPublicationLinkCheck"}), timeout=30) as response:
            published = response.read()
        if published != (ROOT / name).read_bytes():
            raise ValueError(f"Published source differs from locally checked source: {name}")
    result = json.loads((ROOT / "lean/evidence/build_results.json").read_text())
    if result.get("status") != "PASS":
        raise ValueError("Run the publication audit first")
    for name, expected in result["source_sha256"].items():
        if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != expected:
            raise ValueError(f"Audit no longer matches source: {name}")
    lines = (ROOT / files[0]).read_text().splitlines()
    proof = {}
    for name in ["extended_permanence", "measurable_extended_permanence"]:
        line = next(i for i,s in enumerate(lines,1) if s.startswith("theorem "+name+" :"))
        proof[name] = f"{repo}/blob/{revision}/{files[0]}#L{line}"
    raw = f"https://raw.githubusercontent.com{url.path}/{revision}/{files[1]}"
    live = "https://live.lean-lang.org/#url=" + quote(raw, safe="")
    print(json.dumps({"repository": repo, "proof_commit": revision,
                      "proofs": proof, "lean4web": live}, indent=2))
    if args.dry_run:
        return
    start, end = "<!-- PUBLICATION-LINKS:START -->", "<!-- PUBLICATION-LINKS:END -->"
    block = (start + "\n**Try it in Lean4Web:** [open the complete proof in one file](" + live +
             ") (Mathlib with Lean **v4.35.0-rc4**).\n\n" +
             "[Original-rate target proof](" + proof["extended_permanence"] + ") · " +
             "[Measurable common-box proof](" + proof["measurable_extended_permanence"] +
             ")\n" + end)
    edits = {}
    for name in ["README.md", "lean4web/README.md", "FClikelean/README.md"]:
        p = ROOT / name
        text, count = re.subn(re.escape(start)+r"[\s\S]*?"+re.escape(end),
                              lambda _: block, p.read_text())
        if count != 1:
            raise ValueError(f"Expected one publication-links block: {name}")
        edits[p] = text
    p = ROOT / "FClikelean/EndotacticPermanence.lean"
    text = p.read_text()
    for name, link in proof.items():
        pattern = (r'@\[category research solved, AMS 34 92'
                   r'(?:,\s*formal_proof using lean4 at "[^"]+")?\]\s*'
                   r'(?=theorem '+re.escape(name)+r'\s*:)')
        text, count = re.subn(pattern, lambda _: (
            '@[category research solved, AMS 34 92,\n'
            '    formal_proof using lean4 at "'+link+'"]\n'), text)
        if count != 1:
            raise ValueError(f"Expected one FC attribute block: {name}")
    edits[p] = text
    metadata = json.loads((ROOT / "publication.json").read_text())
    metadata.update({"repository_url": repo, "public_proof_commit": revision,
                     "published_sources_verified": True, "proof_links": proof, "lean4web_link": live})
    for p,text in edits.items():
        p.write_text(text)
    (ROOT / "publication.json").write_text(json.dumps(metadata, indent=2)+"\n")
    print("Filled verified public links. Rerun the audit for the edited FC attributes; no push or PR performed.")


if __name__ == "__main__":
    main()
