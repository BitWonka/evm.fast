#!/usr/bin/env python3
"""Validate a frozen init-e submission tree before compiling candidate Lean."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
from pathlib import Path

MAX_FILES = 65536
MAX_FILE_BYTES = 16 * 1024 * 1024
MAX_TOTAL_BYTES = 4 * 1024 * 1024 * 1024
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
COMMENT_OUTSIDE = re.compile(r"/-|--")
COMMENT_INSIDE = re.compile(r"/-|-/")
INTEGER = re.compile(r"0|[1-9][0-9]*")
CLAIM_KEYS = {"K"}
ALLOWED_LIBRARIES = ("Mathlib", "Flapjack", "RiscvZkvm", "Sail", "Batteries", "Lean", "Init", "Std")
TRUSTED_ROOT = Path(__file__).resolve().parent.parent
FROZEN_MANIFEST_NAME = "frozen-submission.json"


def is_editable(rel: Path) -> bool:
    return rel.as_posix() in {"Solution.lean", "claim.json"} or rel.parts[:2] == ("InitECandidate", "Solver")


def hash_frozen_dir(digest, posix: str) -> None:
    digest.update(b"D\0" + posix.encode() + b"\0")


def hash_frozen_file(digest, posix: str, size: int, file_digest: bytes) -> None:
    digest.update(b"F\0" + posix.encode() + f"\0{size}\0".encode() + file_digest)


def frozen_submission_manifest(root: Path) -> dict[str, int | str]:
    """Hash non-editable entries in sorted pre-order (must match verify.freeze_submission)."""
    digest = hashlib.sha256()
    entries = files = total = 0

    def visit(directory: Path, prefix: tuple[str, ...]) -> None:
        nonlocal entries, files, total
        with os.scandir(directory) as listing:
            children = sorted(listing, key=lambda entry: entry.name)
        for entry in children:
            parts = (*prefix, entry.name)
            rel = Path(*parts)
            if is_editable(rel):
                continue
            entries += 1
            posix = "/".join(parts)
            if entry.is_symlink():
                raise ValueError(f"{posix}: symlinks and special files are forbidden")
            if entry.is_dir(follow_symlinks=False):
                hash_frozen_dir(digest, posix)
                visit(Path(entry.path), parts)
            elif entry.is_file(follow_symlinks=False):
                files += 1
                size = entry.stat(follow_symlinks=False).st_size
                total += size
                with open(entry.path, "rb") as stream:
                    file_digest = hashlib.file_digest(stream, "sha256").digest()
                hash_frozen_file(digest, posix, size, file_digest)
            else:
                raise ValueError(f"{posix}: symlinks and special files are forbidden")

    visit(root, ())
    return {"entries": entries, "files": files, "bytes": total, "sha256": digest.hexdigest()}


def load_frozen_manifest(path: Path) -> dict[str, int | str]:
    manifest = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_keys)
    keys = {"entries", "files", "bytes", "sha256"}
    if not isinstance(manifest, dict) or set(manifest) != keys:
        raise ValueError("frozen submission manifest must contain entries, files, bytes and sha256")
    for key in ("entries", "files", "bytes"):
        if type(manifest[key]) is not int or manifest[key] < 0:
            raise ValueError(f"frozen submission manifest {key} must be a nonnegative integer")
    sha = manifest["sha256"]
    if not isinstance(sha, str) or not re.fullmatch(r"[0-9a-f]{64}", sha):
        raise ValueError("frozen submission manifest sha256 must be a lowercase SHA-256 hex digest")
    return manifest


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
    while True:
        match = (COMMENT_INSIDE if depth else COMMENT_OUTSIDE).search(source, i)
        if match is None:
            if depth:
                raise ValueError("unclosed block comment")
            out.append(source[i:])
            return "".join(out)
        pos, token = match.start(), match.group()
        if depth:
            out.append("\n" * source.count("\n", i, pos) + " ")
            depth += 1 if token == "/-" else -1
            i = pos + 2
        elif token == "--":
            out.append(source[i:pos])
            end = source.find("\n", pos + 2)
            i = len(source) if end == -1 else end
        else:
            out.append(source[i:pos] + " ")
            depth = 1
            i = pos + 2


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
    if len(raw) > 128:
        raise ValueError("claim.json exceeds 128 bytes")
    value = json.loads(raw, object_pairs_hook=unique_keys)
    if not isinstance(value, dict) or set(value) != CLAIM_KEYS:
        raise ValueError('claim.json must contain exactly K')
    score = value["K"]
    if score != "infinity" and (type(score) is not int or score < 0):
        raise ValueError('K must be a nonnegative JSON integer or "infinity"')
    return value


def score_literal(values: dict) -> str:
    return ".infinity" if values["K"] == "infinity" else f'.finite {values["K"]}'


def check(root: Path, trusted: Path = TRUSTED_ROOT, *,
          frozen_verified: bool = False) -> dict:
    errors = []
    if root.is_symlink() or not root.is_dir():
        return {"ok": False, "errors": ["submission root is not a directory"]}
    files = sorted(root.rglob("*"))
    if len(files) > MAX_FILES:
        errors.append(f"more than {MAX_FILES} entries")
    total = 0
    lean_files: list[tuple[Path, Path]] = []
    for path in files:
        rel = path.relative_to(root)
        info = path.lstat()
        if stat.S_ISDIR(info.st_mode):
            if rel.parts[0] != "InitECandidate":
                errors.append(f"{rel}: only InitECandidate/ may contain modules")
            continue
        if not stat.S_ISREG(info.st_mode):
            errors.append(f"{rel}: symlinks and special files are forbidden")
            continue
        if rel.as_posix() not in {"Solution.lean", "claim.json"} and not (
            rel.parts[0] == "InitECandidate" and path.suffix == ".lean" and
            all(MODULE.fullmatch(part) for part in rel.with_suffix("").parts)):
            errors.append(f"{rel}: only Solution.lean, claim.json, and InitECandidate modules are admitted")
            continue
        if path.suffix == ".lean":
            lean_files.append((path, rel))
        size = info.st_size
        total += size
        if size > MAX_FILE_BYTES:
            errors.append(f"{rel}: file exceeds 16 MiB")
    if total > MAX_TOTAL_BYTES:
        errors.append("submission exceeds 4 GiB")
    solution = root / "Solution.lean"
    if solution.is_symlink() or not solution.is_file():
        errors.append("Solution.lean is required")
    try:
        claim_path = root / "claim.json"
        if claim_path.is_symlink():
            raise ValueError("claim.json must be a regular file")
        values = claim(claim_path)
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as exc:
        values = None
        errors.append(f"invalid claim.json: {exc}")
    allowed_contract = contract_modules(trusted)
    modules = {".".join(rel.with_suffix("").parts) for _, rel in lean_files}
    for path, rel in lean_files:
        if frozen_verified and not is_editable(rel):
            continue
        try:
            source = path.read_text(encoding="utf-8")
            for module in imports(source):
                if module in allowed_contract or module in modules or any(
                    module == library or module.startswith(library + ".") for library in ALLOWED_LIBRARIES):
                    continue
                errors.append(f"{rel}: import {module} is outside the allowed modules")
        except (OSError, UnicodeError, ValueError) as exc:
            errors.append(f"{rel}: invalid Lean source: {exc}")
    return {"ok": not errors, "claim": values, "score": values["K"] if values else None,
            "files": len(files), "bytes": total, "errors": errors}


def validate_frozen_tree(root: Path, trusted: Path = TRUSTED_ROOT) -> None:
    result = check(root, trusted, frozen_verified=False)
    if not result["ok"]:
        raise ValueError("; ".join(result["errors"]))
    for path in sorted(root.rglob("*.lean")):
        rel = path.relative_to(root)
        if is_editable(rel):
            continue
        for module in imports(path.read_text(encoding="utf-8")):
            if module == "Solution" or module == "InitECandidate.Solver" or module.startswith("InitECandidate.Solver."):
                raise ValueError(f"{rel}: frozen module may not import editable module {module}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("--write-frozen-manifest", action="store_true",
                        help="write verifier/frozen-submission.json from root")
    args = parser.parse_args()
    if args.write_frozen_manifest:
        validate_frozen_tree(args.root, TRUSTED_ROOT)
        manifest = frozen_submission_manifest(args.root)
        target = TRUSTED_ROOT / "verifier" / FROZEN_MANIFEST_NAME
        target.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(json.dumps(manifest, sort_keys=True))
        raise SystemExit(0)
    result = check(args.root)
    print(json.dumps(result, sort_keys=True))
    raise SystemExit(0 if result["ok"] else 1)
