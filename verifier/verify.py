#!/usr/bin/env python3
"""Check a frozen init-e submission against the independently frozen challenge contract.

Untrusted Lean is compiled only within the mandatory Linux systemd/Landlock sandbox.
Structural checks alone never produce the status "verified".
"""
from __future__ import annotations

import argparse
import ctypes
from contextlib import contextmanager
import hashlib
import stat
import json
import os
import platform
import re
import selectors
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import uuid
from pathlib import Path
from typing import BinaryIO

from check_submission import (
    FROZEN_MANIFEST_NAME, MAX_FILES, MAX_FILE_BYTES, MAX_TOTAL_BYTES,
    check, hash_frozen_dir, hash_frozen_file, is_editable, load_frozen_manifest, score_literal,
)

HERE = Path(__file__).resolve().parent
TRUSTED = HERE.parent
LOG_CAP = 4 * 1024 * 1024
MAX_CPUS = 30
MEMORY_BYTES = 112 * 1024**3


class VerifyError(ValueError):
    pass


def tools_env(root: Path) -> dict[str, str]:
    path = root / 'verifier' / '.tools' / 'env.sh'
    if not path.is_file():
        raise VerifyError('verification tools missing; run verifier/setup_tools.sh')
    values = {}
    for line in path.read_text().splitlines():
        if line.startswith('export ') and '=' in line:
            name, value = line[7:].split('=', 1)
            values[name] = value.strip().strip('"')
    for name in ('COMPARATOR_BIN', 'COMPARATOR_LEAN4EXPORT', 'COMPARATOR_LANDRUN', 'COMPARATOR_NANODA'):
        file = Path(values.get(name, ''))
        if not file.is_absolute() or not file.is_file() or not os.access(file, os.X_OK):
            raise VerifyError(f'{name} must point to an installed executable')
    return values


def clone_tree(src: Path, dst: Path) -> None:
    if platform.system() == 'Darwin':
        cmd = ['cp', '-c', '-R', str(src), str(dst)]
    else:
        cmd = ['cp', '-a', '--reflink=auto', str(src), str(dst)]
    subprocess.run(cmd, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)


def link_or_clone_tree(src: Path, dst: Path) -> None:
    try:
        shutil.copytree(src, dst, copy_function=os.link)
    except OSError:
        shutil.rmtree(dst, ignore_errors=True)
        clone_tree(src, dst)


def link_or_copy_file(src: Path, dst: Path) -> None:
    try:
        os.link(src, dst)
    except OSError:
        shutil.copy2(src, dst)


def linux_preflight(env: dict[str, str]) -> None:
    if os.geteuid() == 0:
        raise VerifyError('refusing to compile candidate code as root')
    if not shutil.which('systemd-run') or not shutil.which('systemctl'):
        raise VerifyError('systemd user services are required on Linux')
    lsm = Path('/sys/kernel/security/lsm')
    if not lsm.is_file() or 'landlock' not in lsm.read_text().strip().split(','):
        raise VerifyError('Landlock is not enabled')
    if Path(env['COMPARATOR_LANDRUN']).open('rb').read(4) != b'\x7fELF':
        raise VerifyError('a compiled Landrun binary is required on Linux')
    if platform.machine() not in {'x86_64', 'aarch64', 'riscv64'}:
        raise VerifyError('unsupported Linux architecture')
    libc = ctypes.CDLL(None, use_errno=True)
    libc.syscall.restype = ctypes.c_long
    abi = int(libc.syscall(ctypes.c_long(444), ctypes.c_void_p(), ctypes.c_size_t(0), ctypes.c_uint(1)))
    if abi < 3:
        raise VerifyError('Landlock ABI 3 or newer is required')


def linux_filesystem_type(path: Path) -> int:
    """Read Linux statfs.f_type without relying on the remaining ABI layout."""
    libc = ctypes.CDLL(None, use_errno=True)
    libc.statfs.argtypes = [ctypes.c_char_p, ctypes.c_void_p]
    libc.statfs.restype = ctypes.c_int
    # f_type is the first native long on the supported 64-bit Linux hosts.
    # Leave ample space for the rest of struct statfs, which we do not inspect.
    info = ctypes.create_string_buffer(4096)
    if libc.statfs(os.fsencode(path), info) != 0:
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error), str(path))
    return ctypes.c_ulong.from_buffer(info).value


def validate_spool_directory(spool: Path, project: Path) -> Path:
    if spool.is_symlink() or not spool.is_dir():
        raise VerifyError("comparator spool must be an ordinary private directory")
    spool = spool.resolve()
    if spool.is_relative_to(project.resolve()):
        raise VerifyError("comparator spool must stay outside the staged project")
    info = spool.stat()
    if info.st_uid != os.getuid() or stat.S_IMODE(info.st_mode) != 0o700:
        raise VerifyError("comparator spool must be owned by this user with mode 0700")
    if linux_filesystem_type(spool) in {0x01021994, 0x858458F6}:  # tmpfs, ramfs
        raise VerifyError("comparator spool requires disk-backed storage, not tmpfs or ramfs")
    return spool


@contextmanager
def comparator_spool_directory(work: Path, project: Path):
    # Candidate build sandboxes may write only project/.lake. They neither
    # receive TMPDIR nor gain a write grant to this separate private directory.
    with tempfile.TemporaryDirectory(prefix="comparator-spool-", dir=work) as temporary:
        yield validate_spool_directory(Path(temporary), project)


def linux_command(cmd: list[str], project: Path, env: dict[str, str], hidden: list[Path],
                  wall_seconds: int | None = None, *,
                  spool_dir: Path | None = None) -> tuple[list[str], dict[str, str]]:
    unit = 'init-e-verify-' + uuid.uuid4().hex[:12]
    # Lake scales parallel builds to visible CPUs. Cap the verifier at 30
    # logical CPUs (or fewer if the host affinity provides fewer).
    cpus = sorted(os.sched_getaffinity(0))[:MAX_CPUS]
    properties = [f'MemoryMax={MEMORY_BYTES}', 'MemorySwapMax=0',
                  f'RuntimeMaxSec={wall_seconds if wall_seconds is not None else "infinity"}',
                  f'CPUAffinity={" ".join(map(str, cpus))}',
                  'KillMode=control-group', 'TimeoutStopSec=5', 'SendSIGKILL=yes', 'TasksMax=16384',
                  'RestrictAddressFamilies=~AF_UNIX', 'NoNewPrivileges=yes', 'ProtectSystem=strict',
                  f'ReadWritePaths={project / ".lake"}', 'PrivateTmp=yes', 'PrivateUsers=yes', 'PrivatePIDs=yes', 'ProcSubset=pid',
                  'ReadOnlyPaths=/home',
                  'InaccessiblePaths=/sys',
                  'InaccessiblePaths=' + ' '.join(f'-{p}' for p in ['/etc/ots', '/etc/init-e', *hidden]),
                  'PrivateDevices=yes', 'TemporaryFileSystem=/dev/shm', 'PrivateIPC=yes',
                  'SystemCallErrorNumber=EPERM',
                  'SystemCallFilter=~@network-io @debug ptrace process_vm_readv process_vm_writev '
                  'pidfd_getfd kill tkill tgkill pidfd_send_signal']
    clean = {'PATH': f'{Path.home() / ".elan/bin"}:{os.environ.get("PATH", "/usr/bin:/bin")}',
             'HOME': str(Path.home()), 'LANG': 'C.UTF-8', 'LAKE_ARTIFACT_CACHE': 'false',
             'COMPARATOR_LANDRUN': env['COMPARATOR_LANDRUN'],
             'COMPARATOR_LEAN4EXPORT': env['COMPARATOR_LEAN4EXPORT'],
             'COMPARATOR_NANODA': env['COMPARATOR_NANODA'],
             'INIT_E_VERIFIER_HOST_DEV': str(Path('/dev').stat().st_dev),
             'INIT_E_VERIFIER_HOST_PIDNS': str(Path('/proc/self/ns/pid').stat().st_ino),
             'INIT_E_VERIFIER_HOST_SHM_DEV': str(Path('/dev/shm').stat().st_dev)}
    if spool_dir is not None:
        spool_dir = validate_spool_directory(spool_dir, project)
        properties.append(f'ReadWritePaths={spool_dir}')
        clean['TMPDIR'] = str(spool_dir)
    command = ['/usr/bin/env', '-i', *[f'{k}={v}' for k, v in clean.items()],
               sys.executable, str(HERE / 'linux_exec.py'), *cmd]
    runtime = os.environ.get('XDG_RUNTIME_DIR', f'/run/user/{os.getuid()}')
    bus_env = {'PATH': clean['PATH'], 'HOME': clean['HOME'], 'XDG_RUNTIME_DIR': runtime,
               'DBUS_SESSION_BUS_ADDRESS': os.environ.get('DBUS_SESSION_BUS_ADDRESS', f'unix:path={runtime}/bus')}
    return (['systemd-run', '--user', '--wait', '--collect', '--pipe', '--quiet', f'--unit={unit}',
             f'--working-directory={project}',
             *[arg for prop in properties for arg in ('-p', prop)], '--', *command], bus_env)


def run_checked(cmd: list[str], cwd: Path, env: dict[str, str], log: Path,
                wall_seconds: int | None = None,
                progress_stream: BinaryIO | None = None) -> tuple[int, bool]:
    """Capture at most LOG_CAP bytes of the log tail while draining all output.

    Kill the process group at the outer deadline, as for uncapped output.
    """
    proc = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            start_new_session=True, bufsize=0)
    started = time.monotonic()
    deadline = time.monotonic() + wall_seconds + 120 if wall_seconds is not None else None
    next_heartbeat = started + 30
    truncated = False
    timed_out = False
    try:
        os.set_blocking(proc.stdout.fileno(), False)
        with selectors.DefaultSelector() as selector, log.open('wb') as output:
            selector.register(proc.stdout, selectors.EVENT_READ)
            tail = bytearray()
            while True:
                now = time.monotonic()
                if progress_stream is not None and now >= next_heartbeat:
                    progress_stream.write(f"[verifier] still running ({int(now - started)}s elapsed)\n".encode())
                    progress_stream.flush()
                    next_heartbeat = now + 30
                remain = deadline - time.monotonic() if deadline is not None else None
                if remain is not None and remain <= 0:
                    timed_out = True
                    break
                wait = min(remain, 30) if remain is not None else 30
                if progress_stream is not None:
                    wait = min(wait, max(0, next_heartbeat - time.monotonic()))
                if not selector.select(wait):
                    continue
                try:
                    chunk = os.read(proc.stdout.fileno(), 65536)
                except BlockingIOError:
                    continue
                if not chunk:
                    break
                if progress_stream is not None:
                    progress_stream.write(chunk)
                    progress_stream.flush()
                tail.extend(chunk)
                if len(tail) > LOG_CAP:
                    del tail[:len(tail) - LOG_CAP]
                    truncated = True
            if truncated:
                marker = b'[output truncated; retaining final log bytes]\n'
                output.write(marker[:LOG_CAP])
                output.write(tail[-max(0, LOG_CAP - len(marker)):]
                             if LOG_CAP > len(marker) else b'')
            else:
                output.write(tail)
        if not timed_out:
            proc.wait(timeout=max(.1, deadline - time.monotonic()) if deadline is not None else None)
    except subprocess.TimeoutExpired:
        timed_out = True
    finally:
        if timed_out:
            try:
                os.killpg(proc.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
        proc.stdout.close()
    return proc.returncode, timed_out


def sandbox_probe(env: dict[str, str]) -> None:
    """Exercise mandatory isolation before staging the large trusted build cache."""
    # PrivateTmp hides host /tmp, including probe paths created there.
    with tempfile.TemporaryDirectory(prefix="init-e-isolation-", dir=HERE) as temporary:
        work = Path(temporary)
        project = work / "project"
        project.mkdir()
        (project / ".lake").mkdir()
        command, clean = linux_command(["/usr/bin/true"], project, env, [])
        code, timeout = run_checked(command, project, clean, work / "probe.log")
        if timeout or code != 0:
            detail = (work / "probe.log").read_text(errors="replace")[-1000:].strip()
            raise VerifyError(f"mandatory Linux isolation preflight failed: {detail}")


def freeze_submission(source: Path, target: Path,
                      manifest_path: Path | None = None) -> bool:
    """Bounded fd-relative copy: no links, devices, FIFOs or followed directory races."""
    expected = None
    if manifest_path is not None:
        if manifest_path.is_symlink() or not manifest_path.is_file():
            raise VerifyError(f"missing frozen submission manifest: {manifest_path}")
        try:
            expected = load_frozen_manifest(manifest_path)
        except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as exc:
            raise VerifyError(f"invalid frozen submission manifest: {exc}") from exc
    target.mkdir()
    entries = total = frozen_entries = frozen_files = frozen_bytes = 0
    frozen_digest = hashlib.sha256()
    directory_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    def visit(fd: int, destination: Path, prefix: tuple[str, ...]):
        nonlocal entries, total, frozen_entries, frozen_files, frozen_bytes
        for name in sorted(os.listdir(fd)):
            entries += 1
            if entries > MAX_FILES:
                raise VerifyError(f"submission has more than {MAX_FILES} entries")
            rel = Path(*prefix, name)
            editable = is_editable(rel)
            if expected is not None and not editable:
                frozen_entries += 1
            info = os.stat(name, dir_fd=fd, follow_symlinks=False)
            path = destination / name
            if stat.S_ISDIR(info.st_mode):
                if expected is not None and not editable:
                    hash_frozen_dir(frozen_digest, rel.as_posix())
                child = os.open(name, directory_flags, dir_fd=fd)
                try:
                    path.mkdir()
                    visit(child, path, (*prefix, name))
                finally:
                    os.close(child)
            elif stat.S_ISREG(info.st_mode):
                child = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=fd)
                try:
                    if not stat.S_ISREG(os.fstat(child).st_mode):
                        raise VerifyError("submission entry changed to a special file")
                    with os.fdopen(child, "rb", closefd=False) as stream:
                        data = stream.read(MAX_FILE_BYTES + 1)
                finally:
                    os.close(child)
                if len(data) > MAX_FILE_BYTES:
                    raise VerifyError(f"{name}: file exceeds {MAX_FILE_BYTES} bytes")
                total += len(data)
                if total > MAX_TOTAL_BYTES:
                    raise VerifyError(f"submission exceeds {MAX_TOTAL_BYTES} bytes")
                if expected is not None and not editable:
                    frozen_files += 1
                    frozen_bytes += len(data)
                    hash_frozen_file(frozen_digest, rel.as_posix(), len(data), hashlib.sha256(data).digest())
                path.write_bytes(data)
            else:
                raise VerifyError(f"{name}: symlinks and special files are forbidden")
    root = os.open(source, directory_flags)
    try:
        visit(root, target, ())
    finally:
        os.close(root)
    return expected is not None and {
        "entries": frozen_entries,
        "files": frozen_files,
        "bytes": frozen_bytes,
        "sha256": frozen_digest.hexdigest(),
    } == expected


REBUILT_NAMESPACES = (
    "Guest", "InitE", "InitECandidate", "Solution",
    "Submission", "TrustedAxioms", "VerifierChallenge",
)


def clone_project_cache(source: Path, target: Path) -> None:
    """Copy useful caches without first copying artifacts we must discard."""
    # These generated launchers contain absolute links to the original cache.
    # The verifier recreates its own limiter inside the staged writable tree.
    ephemeral_roots = {"lean-limit", "metadata-limit"}
    artifact_roots = {Path("build/lib/lean"), Path("build/ir")}
    traversed = {Path("."), Path("build"), Path("build/lib"), *artifact_roots}

    def visit(current: Path, destination: Path, relative: Path) -> None:
        if relative not in traversed:
            clone_tree(current, destination)
            return
        if current.is_symlink() or not current.is_dir():
            raise VerifyError(f"trusted cache directory is not an ordinary directory: {relative}")
        destination.mkdir()
        for child in current.iterdir():
            if relative == Path(".") and child.name in ephemeral_roots:
                continue
            if relative in artifact_roots and any(
                child.name == name or child.name.startswith(name + ".")
                for name in REBUILT_NAMESPACES
            ):
                continue
            visit(child, destination / child.name, relative / child.name)
        shutil.copystat(current, destination)

    visit(source, target, Path("."))


def clear_artifacts(project: Path, names: tuple[str, ...]) -> None:
    for folder in (project / ".lake" / "build" / "lib" / "lean", project / ".lake" / "build" / "ir"):
        for name in names:
            tree = folder / name
            if tree.is_dir():
                shutil.rmtree(tree)
            for stale in folder.glob(f"{name}.*"):
                stale.unlink()


def prepare_project(trusted: Path, source: Path, project: Path, values: dict, *,
                    link_source: bool = False) -> str:
    """Freeze only the challenge contract, then copy the untrusted submission."""
    helpers = ("lean-process-limit.c", "limited-lake.py")
    for name in helpers:
        if not (trusted / "tools" / name).is_file():
            raise VerifyError(f"trusted Lean limiter source missing: tools/{name}")
    project.mkdir()
    (project / "tools").mkdir()
    for name in helpers:
        shutil.copy2(trusted / "tools" / name, project / "tools" / name)
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "Guest.lean"):
        shutil.copy2(trusted / name, project / name)
    if (trusted / "InitE.lean").is_file():
        shutil.copy2(trusted / "InitE.lean", project / "InitE.lean")
    for directory in ("Guest", "InitE"):
        if not (trusted / directory).is_dir():
            continue
        for path in (trusted / directory).rglob("*.lean"):
            destination = project / path.relative_to(trusted)
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, destination)
    (project / "Guest").mkdir(exist_ok=True)
    shutil.copy2(trusted / "Guest" / "guest.pp.pnk", project / "Guest" / "guest.pp.pnk")
    with (project / "lakefile.toml").open("a") as out:
        out.write('\n[[lean_lib]]\nname = "VerifierChallenge"\nsrcDir = "verifier"\n')
    (project / "verifier").mkdir()
    for name in ("TrustedAxioms.lean", "trusted-axioms.json", "comparator.json"):
        shutil.copy2(trusted / "verifier" / name, project / "verifier" / name)
    template = (trusted / "verifier" / "Challenge.lean.in").read_text()
    (project / "verifier" / "VerifierChallenge.lean").write_text(template.replace("{{SCORE}}", score_literal(values)))
    # Hash only trusted challenge source/configuration, before copying candidate files.
    digest = hashlib.sha256()
    for path in sorted(project.rglob("*")):
        if path.is_file():
            digest.update(path.relative_to(project).as_posix().encode() + b"\0")
            digest.update(path.read_bytes() + b"\0")
    (project / "submission").mkdir()
    if link_source:
        link_or_copy_file(source / "Solution.lean", project / "submission" / "Solution.lean")
        if (source / "InitECandidate").is_dir():
            link_or_clone_tree(source / "InitECandidate", project / "submission" / "InitECandidate")
    else:
        shutil.copy2(source / "Solution.lean", project / "submission" / "Solution.lean")
        if (source / "InitECandidate").is_dir():
            clone_tree(source / "InitECandidate", project / "submission" / "InitECandidate")
    clone_project_cache(trusted / ".lake", project / ".lake")
    # Defense in depth: renamed imports must rebuild, independently of cache copying.
    clear_artifacts(project, REBUILT_NAMESPACES)
    return digest.hexdigest()


STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


def trusted_axioms(log: str, manifest: Path | None = None) -> list[str]:
    markers = re.findall(r"INIT_E_TRUSTED_AXIOMS (\[[^\n]*\])", log)
    if len(markers) != 1:
        raise VerifyError("trusted axiom audit did not produce exactly one manifest")
    names = json.loads(markers[0])
    if not isinstance(names, list) or not all(isinstance(name, str) for name in names):
        raise VerifyError("trusted axiom manifest is malformed")
    if len(names) != len(set(names)):
        raise VerifyError("trusted axiom manifest contains duplicate names")
    manifest = manifest or Path(__file__).with_name("trusted-axioms.json")
    pinned = json.loads(manifest.read_text())
    if not isinstance(pinned, list) or not all(isinstance(name, str) for name in pinned):
        raise VerifyError("pinned trusted axiom manifest is malformed")
    if len(pinned) != len(set(pinned)) or set(pinned) != STANDARD_AXIOMS:
        raise VerifyError("trusted manifest must contain exactly the three standard Lean axioms")
    # Exact equality with the standard axioms: neither challenge computations
    # nor candidate names can add an axiom permission.
    if set(names) != set(pinned):
        unexpected = sorted(set(names) - set(pinned))
        missing = sorted(set(pinned) - set(names))
        raise VerifyError(f"trusted axiom closure changed: unexpected={unexpected}, missing={missing}")
    return sorted(pinned)


def limited_lake_command(project: Path, command: list[str]) -> list[str]:
    """Run with trusted project-local sources and writable admission locks."""
    return [sys.executable, str(project / "tools" / "limited-lake.py"),
            "--work-dir", str(project / ".lake" / "lean-limit"),
            "--slots", str(MAX_CPUS), "--", *command]


def verify(args: argparse.Namespace) -> dict:
    work = args.work.resolve()
    if work.exists():
        raise VerifyError("work directory must not exist")
    work.mkdir(parents=True)
    log = work / "verify.log"
    result = {"status": "failed", "log": str(log), "claim": None, "contract_sha256": None}
    def progress(message: str) -> None:
        if args.progress:
            print(f"[verifier] {message}", file=sys.stderr, flush=True)

    try:
        source = work / "source"
        progress("freezing submission")
        frozen_verified = freeze_submission(
            args.local, source, args.trusted / "verifier" / FROZEN_MANIFEST_NAME
        )
        progress("checking submission policy")
        policy = check(source, args.trusted, frozen_verified=frozen_verified)
        result["claim"] = policy["claim"]
        if not frozen_verified:
            policy = dict(
                policy, ok=False,
                errors=["non-editable submission files differ from verifier/frozen-submission.json", *policy["errors"]],
            )
        if not policy["ok"]:
            log.write_text("\n".join(policy["errors"]) + "\n")
            return dict(result, status="policy_rejected", errors=policy["errors"])
        if args.structural_only:
            log.write_text("File/import/claim policy accepted; no proof verification was performed.\n")
            return dict(result, status="structural_pass", score=policy["score"],
                        reason="File/import/claim checks only; no proof verification was performed.")
        if platform.system() != "Linux":
            raise VerifyError("isolated proof verification currently requires Linux")
        env = tools_env(args.trusted)
        linux_preflight(env)
        progress("checking mandatory isolation")
        sandbox_probe(env)
        project = work / "project"
        progress("staging project and trusted cache")
        result["contract_sha256"] = prepare_project(
            args.trusted, source, project, policy["claim"], link_source=True
        )
        # Trusted audit runs first and imports only the independently frozen challenge.
        audit_log = work / "trusted-audit.log"
        audit_command = limited_lake_command(project, ["lake", "build", "TrustedAxioms"])
        command, clean = linux_command(audit_command, project, env,
                                       [source, *args.hide])
        progress("building trusted axiom audit")
        code, timeout = run_checked(command, project, clean, audit_log,
                                    progress_stream=sys.stderr.buffer if args.progress else None)
        if timeout or code != 0:
            return dict(result, status="trusted_build_failed", audit_log=str(audit_log), timed_out=timeout,
                        reason=audit_log.read_text(errors="replace")[-1200:])
        permitted = trusted_axioms(audit_log.read_text(errors="replace"),
                                  project / "verifier" / "trusted-axioms.json")
        config = json.loads((project / "verifier" / "comparator.json").read_text())
        config["permitted_axioms"] = permitted
        config["enable_nanoda"] = False
        config_path = work / "comparator.json"
        config_path.write_text(json.dumps(config, indent=2) + "\n")
        result["permitted_axioms"] = permitted
        comparator_command = limited_lake_command(
            project, ["lake", "env", env["COMPARATOR_BIN"], str(config_path)])
        with comparator_spool_directory(work, project) as spool_dir:
            command, clean = linux_command(comparator_command, project, env,
                                           [source, *args.hide], spool_dir=spool_dir)
            progress("running comparator")
            code, timeout = run_checked(command, project, clean, log,
                                        progress_stream=sys.stderr.buffer if args.progress else None)
            output = log.read_text(errors="replace")
            if timeout:
                return dict(result, status="timeout")
            if code == 0 and "Your solution is okay!" in output:
                return dict(result, status="verified", score=policy["score"])
            return dict(result, status="rejected", reason=output[-1200:])
    except (VerifyError, OSError, subprocess.SubprocessError, ValueError) as exc:
        log.write_text(str(exc) + "\n")
        return dict(result, status="failed", reason=str(exc)[:1200])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--local", type=Path, required=True, help="submission directory")
    parser.add_argument("--trusted", type=Path, default=TRUSTED)
    parser.add_argument("--work", type=Path)
    parser.add_argument("--hide", type=Path, action="append", default=[])
    parser.add_argument("--structural-only", action="store_true")
    parser.add_argument("--progress", action="store_true",
                        help="show stages and stream build/comparator output to stderr")
    args = parser.parse_args()
    args.trusted = args.trusted.resolve()
    if args.work is None:
        run_root = HERE / "runs"
        run_root.mkdir(parents=True, exist_ok=True)
        args.work = Path(tempfile.mkdtemp(prefix="init-e-verify-", dir=run_root))
        args.work.rmdir()
    try:
        result = verify(args)
    except (VerifyError, OSError) as exc:
        result = {"status": "failed", "reason": str(exc)}
    print(json.dumps(result, sort_keys=True))
    return 0 if result["status"] == "verified" or (args.structural_only and result["status"] == "structural_pass") else 1


if __name__ == "__main__":
    raise SystemExit(main())
