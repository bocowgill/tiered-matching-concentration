#!/usr/bin/env python3
"""Check statement provenance, source limits, pins and local documentation links.

This is an author-side check. Palomar's complete mechanical workflow remains
the authoritative preparatory check for a candidate commit.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def statement(text: str) -> str:
    header = re.search(r"theorem (?:_root_\.TieredMatching\.)?match_type_concentration\n", text)
    assert header, "Missing concentration theorem"
    start = header.end()
    end = text.index(" := by", start)
    return " ".join(text[start:end].split())


def strip_comments(text: str) -> str:
    out = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        else:
            out.append(text[i])
            i += 1
    assert depth == 0, "Unclosed block comment"
    return "".join(out)


def main() -> None:
    bindings = json.loads((ROOT / "provenance/source-bindings.json").read_text())
    for item in bindings["files"]:
        assert hashlib.sha256((ROOT / item["snapshot"]).read_bytes()).hexdigest() == item["sha256"]
    original = (ROOT / "provenance/TieredRandomMatching.lean.txt").read_text()
    for filename in ["Challenge.lean", "Solution.lean"]:
        assert statement((ROOT / filename).read_text()) == statement(original), filename
    challenge = (ROOT / "Challenge.lean").read_text()
    assert re.findall(r"^public import (.+)$", challenge, re.M) == ["Mathlib"]
    assert len(challenge.encode()) <= 100 * 1024
    assert len(challenge.splitlines()) <= 1000
    # Verify the admission detector against a positive control before using it.
    forbidden = re.compile(r"\b(sorry|admit|axiom|native_decide|sorryAx|ofReduceBool)\b")
    assert forbidden.search(strip_comments("/-- audit --/ theorem x : True := by sorry"))
    assert not forbidden.search(strip_comments("/- sorry -/ theorem x : True := by trivial"))
    lean_files = sorted(p for p in ROOT.rglob("*.lean") if ".lake" not in p.parts)
    for path in lean_files:
        if path.name != "Challenge.lean":
            assert not forbidden.search(strip_comments(path.read_text())), path.relative_to(ROOT)
    subprocess.run(["python3", "scripts/check-lean-sources.py"], cwd=ROOT, check=True)
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        assert package["type"] == "git"
        assert re.fullmatch(r"[0-9a-f]{40}", package["rev"])
        assert re.fullmatch(r"https://github.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", package["url"])
    for path in [ROOT / "README.md", *(ROOT / "docs").glob("*.md")]:
        for target in re.findall(r"\]\(([^)]+)\)", path.read_text()):
            if "://" not in target and not target.startswith("#"):
                assert (path.parent / target.split("#")[0]).exists(), (path.name, target)
    readme = (ROOT / "README.md").read_text()
    assert "Codex helped me formalize the proof in Lean." in readme
    assert "A paper presenting the proof is forthcoming." in readme
    print(f"SUBMISSION_SOURCE_CHECKS_PASSED ({len(lean_files)} Lean files)")


if __name__ == "__main__":
    main()
