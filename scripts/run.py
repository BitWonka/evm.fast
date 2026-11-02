"""Adapt the pinned init-e verifier's accepted certificate to a Yukon score.

INIT_E_VERIFICATION=comparator (default) runs verifier/verify.py unchanged and requires `verified`.
INIT_E_VERIFICATION=build is a faster local check: it reuses the verifier's policy check, isolation
preflight, staging and trusted axiom audit, then builds the candidate in the same sandbox and
checks the pinned statement, the claimed score and the axiom closure. It skips comparator
export and kernel replay, so it trusts that candidate Lean does not tamper with its own build.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import secrets
import subprocess
import sys
import time
import uuid

ROOT = Path(__file__).resolve().parent.parent
# scripts/blacksmith.sh copies the checkout here inside its KVM guest and runs this file there.
GUEST_ROOT = Path("/srv/evm-benchmark")
CPUINFO = Path("/proc/cpuinfo")
sys.path.insert(0, str(ROOT / "verifier"))
import verify  # noqa: E402
from check_submission import FROZEN_MANIFEST_NAME, check, score_literal  # noqa: E402
import time_score  # noqa: E402

CHECK = """import Solution
import Lean.Util.CollectAxioms
import Lean.Elab.Command

example : _root_.InitE.Certificate _root_.InitE.Challenge.submission ({{SCORE}} : _root_.InitE.NatE) :=
  _root_.InitE.Challenge.certificate

open Lean in
run_cmd do
  let env ← getEnv
  let some (.thmInfo _) := env.find? `InitE.Challenge.certificate
    | throwError "InitE.Challenge.certificate must be a theorem"
  let some (.defnInfo _) := env.find? `InitE.Challenge.submission
    | throwError "InitE.Challenge.submission must be a definition"
  let mut names : Array Name := #[]
  for root in #[`InitE.Challenge.certificate, `InitE.Challenge.submission, `InitE.Challenge.claimedScore] do
    for name in (← collectAxioms root) do
      unless names.contains name do names := names.push name
  let json := Json.arr (names.map fun name => Json.str name.toString)
  logInfo m!"INIT_E_YUKON_CHECK {{NONCE}} {json.compress}"
"""


def build_verify(work: Path) -> dict:
    work.mkdir(parents=True)
    result = {"status": "failed", "claim": None, "contract_sha256": None}
    try:
        source = work / "source"
        frozen_verified = verify.freeze_submission(
            ROOT / "submission", source, ROOT / "verifier" / FROZEN_MANIFEST_NAME
        )
        policy = check(source, ROOT, frozen_verified=frozen_verified)
        result["claim"] = policy["claim"]
        if not frozen_verified:
            policy = dict(
                policy, ok=False,
                errors=["non-editable submission files differ from verifier/frozen-submission.json", *policy["errors"]],
            )
        if not policy["ok"]:
            return dict(result, status="policy_rejected", errors=policy["errors"])
        env = verify.tools_env(ROOT)
        verify.linux_preflight(env)
        verify.sandbox_probe(env)
        project = work / "project"
        result["contract_sha256"] = verify.prepare_project(
            ROOT, source, project, policy["claim"], link_source=True
        )

        def sandboxed(name: str, command: list[str]) -> tuple[bool, str]:
            log = work / f"{name}.log"
            # The verifier's own defaults set the unit's time limit, as its comparator run does.
            argv, clean = verify.linux_command(verify.limited_lake_command(project, command), project, env, [source])
            code, timed_out = verify.run_checked(argv, project, clean, log)
            return code == 0 and not timed_out, log.read_text(errors="replace")

        ok, audit = sandboxed("trusted-audit", ["lake", "build", "TrustedAxioms"])
        if not ok:
            return dict(result, status="trusted_build_failed", reason=audit[-1200:])
        permitted = verify.trusted_axioms(audit, project / "verifier" / "trusted-axioms.json")
        result["permitted_axioms"] = permitted
        ok, build = sandboxed("candidate-build", ["lake", "build", "Submission"])
        if not ok:
            return dict(result, status="rejected", reason=build[-1200:])
        # Written after the candidate build so candidate code never sees this run's nonce.
        nonce = secrets.token_hex(16)
        (project / "verifier" / "YukonCheck.lean").write_text(
            CHECK.replace("{{SCORE}}", score_literal(policy["claim"])).replace("{{NONCE}}", nonce))
        ok, output = sandboxed("candidate-check", ["lake", "env", "lean", "verifier/YukonCheck.lean"])
        markers = re.findall(rf"INIT_E_YUKON_CHECK {nonce} (\[[^\n]*\])", output)
        if not ok or len(markers) != 1:
            return dict(result, status="rejected", reason=output[-1200:])
        axioms = json.loads(markers[0])
        if not isinstance(axioms, list) or not all(isinstance(name, str) for name in axioms):
            return dict(result, status="rejected", reason="malformed axiom report")
        extra = sorted(set(axioms) - set(permitted))
        if extra:
            return dict(result, status="rejected", reason=f"axioms outside the permitted set: {extra}")
        return dict(result, status="build_checked", score=policy["score"], axioms=sorted(axioms))
    except (verify.VerifyError, OSError, subprocess.SubprocessError, ValueError) as exc:
        return dict(result, status="failed", reason=str(exc)[:1200])


def comparator_verify(work: Path) -> dict:
    # --progress streams stage changes and build output to stderr; the JSON report stays on stdout.
    command = [sys.executable, str(ROOT / "verifier" / "verify.py"), "--local", str(ROOT / "submission"),
               "--trusted", str(ROOT), "--work", str(work), "--progress"]
    return json.loads(subprocess.run(command, stdout=subprocess.PIPE, text=True, cwd=ROOT).stdout)


def runner() -> dict:
    """Non-secret details of the machine that ran the verifier, for comparing verifySeconds.

    In the guest VM these describe the guest: its vCPUs, the host CPU model (-cpu host), and no
    RUNNER_NAME, which neither ssh nor sudo passes in.
    """
    info = {}
    if os.environ.get("RUNNER_NAME"):
        info["name"] = os.environ["RUNNER_NAME"]
    try:
        with CPUINFO.open() as cpuinfo:
            model = next((line.split(":", 1)[1].strip() for line in cpuinfo if line.startswith("model name")), "")
    except OSError:
        model = ""
    if model:
        info["cpuModel"] = model
    info["cpuCount"] = os.cpu_count()
    info["guestVm"] = ROOT == GUEST_ROOT
    return info


def main() -> None:
    score_path = ROOT / "scripts" / "score.json"
    score_path.unlink(missing_ok=True)
    mode = os.environ.get("INIT_E_VERIFICATION", "comparator")
    if mode not in {"comparator", "build"}:
        raise SystemExit("INIT_E_VERIFICATION must be comparator or build")
    if sys.platform != "linux":
        raise SystemExit("Official verification requires Linux; the upstream macOS mode is unsandboxed")
    work = ROOT / "work" / "yukon" / uuid.uuid4().hex
    started = time.monotonic()
    report = comparator_verify(work) if mode == "comparator" else build_verify(work)
    # The score carries these minutes; official runs then apply the record rule (scripts/time_score.py).
    timing = {"verifySeconds": round(time.monotonic() - started, 1), "verifyRunner": runner()}
    print(json.dumps(report, sort_keys=True))
    print(f"Verifier timing: {json.dumps(timing)}", file=sys.stderr)
    if report.get("status") != ("verified" if mode == "comparator" else "build_checked"):
        raise SystemExit(f"Verifier did not accept the submission: {report.get('status')}")
    claim = report["score"]
    if claim == "infinity":
        scored = time_score.INFINITY
    elif type(claim) is int and 0 <= claim <= time_score.LARGEST_K:
        scored = time_score.exact_score(time_score.encode(claim, time_score.minutes(timing["verifySeconds"])))
    else:
        raise SystemExit("K must be below 10^295: a Yukon exact score holds at most 299 integer digits, "
                         "four of them verification minutes")
    contract = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True, cwd=ROOT).strip()
    metrics = {"claim": claim, "finite": claim != "infinity", "verification": mode,
               "comparatorVerified": mode == "comparator", "permittedAxioms": report.get("permitted_axioms"),
               "axioms": report.get("axioms"), "contractSha256": report["contract_sha256"],
               "contractCommit": contract, **timing}
    temporary = score_path.with_suffix(".tmp")
    temporary.write_text(json.dumps({**scored, "metrics": metrics}) + "\n")
    temporary.replace(score_path)


if __name__ == "__main__":
    main()
