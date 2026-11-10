#!/usr/bin/env python3
"""Validate a frozen init-e submission tree before compiling candidate Lean."""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

MAX_FILES = 65536
MAX_FILE_BYTES = 16 * 1024 * 1024
MAX_TOTAL_BYTES = 4 * 1024 * 1024 * 1024
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
INTEGER = re.compile(r"0|[1-9][0-9]*")
CLAIM_KEYS = {"K"}
# {"K":N} for every N below 10^295 (the largest K scoring accepts), plus a newline.
MAX_CLAIM_BYTES = 302
ALLOWED_LIBRARIES = ("Mathlib", "Flapjack", "RiscvZkvm", "Sail", "Batteries", "Lean", "Init", "Std")
TRUSTED_ROOT = Path(__file__).resolve().parent.parent


def contract_modules(trusted: Path) -> set[str]:
    """Only concrete, trusted source modules; no similarly named prefixes."""
    modules = {name for name in ("Guest", "InitE") if (trusted / (name + ".lean")).is_file()}
    for directory in ("Guest", "InitE"):
        modules.update(".".join(path.relative_to(trusted).with_suffix("").parts)
                       for path in (trusted / directory).rglob("*.lean"))
    return modules


def strip_comments(source: str) -> str:
    """Remove nested block and line comments while retaining newlines and token gaps."""
    out = []
    i = depth = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            out.append(" ")
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            out.append(" ")
            i += 2
        elif depth:
            if source[i] == "\n":
                out.append("\n")
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError("unclosed block comment")
    return "".join(out)


def imports(source: str) -> list[str]:
    found = []
    for line in strip_comments(source).lstrip("\ufeff").splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith("prelude") or line.startswith("module "):
            raise ValueError("alternate module headers are not allowed")
        if line.startswith("import"):
            parts = line.split()
            if len(parts) != 2 or not MODULE.fullmatch(parts[1]):
                raise ValueError("each import must name one ordinary ASCII module")
            found.append(parts[1])
            continue
        break
    return found


def unique_keys(pairs):
    value = {}
    for key, item in pairs:
        if key in value:
            raise ValueError(f"duplicate JSON key: {key}")
        value[key] = item
    return value


def claim(path: Path) -> dict[str, int | str]:
    raw = path.read_bytes()
    if len(raw) > MAX_CLAIM_BYTES:
        raise ValueError(f"claim.json exceeds {MAX_CLAIM_BYTES} bytes")
    value = json.loads(raw, object_pairs_hook=unique_keys)
    if not isinstance(value, dict) or set(value) != CLAIM_KEYS:
        raise ValueError('claim.json must contain exactly K')
    score = value["K"]
    if score != "infinity" and (type(score) is not int or score < 0):
        raise ValueError('K must be a nonnegative JSON integer or "infinity"')
    return value


def score_literal(values: dict) -> str:
    return ".infinity" if values["K"] == "infinity" else f'.finite {values["K"]}'


def check(root: Path, trusted: Path = TRUSTED_ROOT) -> dict:
    errors = []
    if root.is_symlink() or not root.is_dir():
        return {"ok": False, "errors": ["submission root is not a directory"]}
    files = sorted(root.rglob("*"))
    if len(files) > MAX_FILES:
        errors.append(f"more than {MAX_FILES} entries")
    total = 0
    for path in files:
        rel = path.relative_to(root)
        if path.is_symlink() or not (path.is_file() or path.is_dir()):
            errors.append(f"{rel}: symlinks and special files are forbidden")
            continue
        if path.is_dir():
            if rel.parts[0] != "InitECandidate":
                errors.append(f"{rel}: only InitECandidate/ may contain modules")
            continue
        if rel.as_posix() not in {"Solution.lean", "claim.json"} and not (
            rel.parts[0] == "InitECandidate" and path.suffix == ".lean" and
            all(MODULE.fullmatch(part) for part in rel.with_suffix("").parts)):
            errors.append(f"{rel}: only Solution.lean, claim.json, and InitECandidate modules are admitted")
            continue
        size = path.stat().st_size
        total += size
        if size > MAX_FILE_BYTES:
            errors.append(f"{rel}: file exceeds 16 MiB")
    if total > MAX_TOTAL_BYTES:
        errors.append("submission exceeds 4 GiB")
    if not (root / "Solution.lean").is_file():
        errors.append("Solution.lean is required")
    try:
        values = claim(root / "claim.json")
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as exc:
        values = None
        errors.append(f"invalid claim.json: {exc}")
    allowed_contract = contract_modules(trusted)
    modules = {".".join(path.relative_to(root).with_suffix("").parts)
               for path in files if path.is_file() and path.suffix == ".lean"}
    for path in files:
        if not path.is_file() or path.suffix != ".lean":
            continue
        try:
            source = path.read_text(encoding="utf-8")
            for module in imports(source):
                if module in allowed_contract or module in modules or any(
                    module == library or module.startswith(library + ".") for library in ALLOWED_LIBRARIES):
                    continue
                errors.append(f"{path.relative_to(root)}: import {module} is outside the allowed modules")
        except (OSError, UnicodeError, ValueError) as exc:
            errors.append(f"{path.relative_to(root)}: invalid Lean source: {exc}")
    return {"ok": not errors, "claim": values, "score": values["K"] if values else None,
            "files": len(files), "bytes": total, "errors": errors}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    args = parser.parse_args()
    result = check(args.root)
    print(json.dumps(result, sort_keys=True))
    raise SystemExit(0 if result["ok"] else 1)
