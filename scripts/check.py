#!/usr/bin/env python3
"""Build the formalization and audit the axioms of the main results."""

from __future__ import annotations

import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {
    "sorry", "admit", "axiom", "axioms", "sorryAx", "native_decide",
    "unsafe", "implemented_by", "extern", "skipKernelTC",
}


def lean_tokens(text: str) -> list[str]:
    """Ignore strings, line comments, and nested block comments before scanning."""
    clean: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            clean.append(" ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
            clean.append("\n")
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            clean.append(" ")
        else:
            clean.append(text[i])
            i += 1
    if depth:
        raise ValueError("unterminated Lean block comment")
    return re.findall(r"[\w.]+", "".join(clean))


def check_sources() -> int:
    sources = sorted((ROOT / "ControlTheory").rglob("*.lean"))
    sources.append(ROOT / "ControlTheory.lean")
    if not sources:
        raise RuntimeError("no Lean sources found")
    for source in sources:
        bad = set(lean_tokens(source.read_text(encoding="utf-8"))) & FORBIDDEN
        if bad:
            raise RuntimeError(f"{source.relative_to(ROOT)}: forbidden tokens {sorted(bad)}")
    return len(sources)


def run(*args: str) -> str:
    print("+", " ".join(args), flush=True)
    result = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, encoding="utf-8")
    print(result.stdout, end="", flush=True)
    if result.returncode:
        raise RuntimeError(f"command exited with status {result.returncode}")
    return result.stdout


def main() -> None:
    count = check_sources()
    if shutil.which("lake") is None:
        raise RuntimeError("lake is not on PATH; install Lean using lean-lang.org/install")
    run("lake", "build")
    output = run("lake", "env", "lean", "Verification.lean")
    if "sorryAx" in output:
        raise RuntimeError("a principal result depends on a proof placeholder")
    expected = re.findall(r"^#print axioms (\S+)",
                          (ROOT / "Verification.lean").read_text(encoding="utf-8"), re.M)
    for name in expected:
        if name not in output:
            raise RuntimeError(f"missing axiom report for {name}")
    reports = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output, re.S)
    empty = len(re.findall(r"does not depend on any axioms", output))
    if len(reports) + empty != len(expected):
        raise RuntimeError("unexpected format or incomplete axiom report")
    for report in reports:
        found = {x.strip() for x in report.split(",") if x.strip()}
        if found - ALLOWED_AXIOMS:
            raise RuntimeError(f"unexpected axioms: {sorted(found - ALLOWED_AXIOMS)}")
    print(f"PASS: {count} Lean source modules; {len(expected)} principal results audited.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
