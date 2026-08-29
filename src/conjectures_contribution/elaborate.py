"""Elaborate a contribution's Lean sources against a prepared toolchain.

This is the only stage that runs contributed code, so it runs last, on the
self-hosted runner, and only after every static rule has passed. Each `.lean`
artifact is elaborated on its own — a contribution is not a Lake package, so it
cannot import a sibling — inside a scratch directory, under a wall-clock timeout,
a memory cap, a deterministic heartbeat budget, and, where the kernel permits an
unprivileged user namespace, with no network.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any, cast

from .checks.base import Finding, Severity
from .lean import LEAN_SUFFIX

CHECK_ID = "L001"
DEFAULT_TIMEOUT_SECONDS = 900
DEFAULT_MEMORY_MB = 8192
DEFAULT_HEARTBEATS = 400_000
TIMEOUT_EXIT_CODE = 124
DETAIL_CHARS = 400
# Lean has spelled this with straight quotes and with backticks.
SORRY_RE = re.compile("uses\\s*['`\u2018]?sorry")
INHERITED_ENV = ("PATH", "HOME", "LANG", "LC_ALL", "ELAN_HOME", "ELAN_TOOLCHAIN")


class WorkspaceError(RuntimeError):
    pass


def network_sandbox() -> list[str]:
    if shutil.which("unshare") is None:
        return []
    probe = subprocess.run(
        ["unshare", "-rn", "true"],  # noqa: S607 - literal argv, resolved on PATH
        capture_output=True,
        check=False,
    )
    return ["unshare", "-rn"] if probe.returncode == 0 else []


def _environment(scratch: Path) -> dict[str, str]:
    env = {name: os.environ[name] for name in INHERITED_ENV if name in os.environ}
    env.setdefault("HOME", str(Path.home()))
    env["TMPDIR"] = str(scratch)
    env["NO_COLOR"] = "1"
    return env


def _diagnostics(stdout: str) -> list[dict[str, Any]]:
    parsed: list[dict[str, Any]] = []
    for line in stdout.splitlines():
        stripped = line.strip()
        if not stripped.startswith("{"):
            continue
        try:
            decoded = json.loads(stripped)
        except json.JSONDecodeError:
            continue
        if isinstance(decoded, dict):
            parsed.append(cast("dict[str, Any]", decoded))
    return parsed


def _finding(severity: Severity, message: str, artifact: str) -> Finding:
    return Finding(CHECK_ID, severity, message, artifact)


def _report_file(artifact: str, result: subprocess.CompletedProcess[str]) -> list[Finding]:
    if result.returncode == TIMEOUT_EXIT_CODE:
        return [_finding(Severity.ERROR, "elaboration hit the wall-clock timeout", artifact)]

    findings: list[Finding] = []
    diagnostics = _diagnostics(result.stdout)
    for diagnostic in diagnostics:
        message = " ".join(str(diagnostic.get("data", "")).split())
        line = diagnostic.get("pos", {}).get("line")
        located = f"line {line}: " if line else ""
        if SORRY_RE.search(message):
            findings.append(_finding(Severity.ERROR, f"{located}{message}", artifact))
        elif diagnostic.get("severity") == "error":
            findings.append(
                _finding(Severity.ERROR, f"{located}{message[:DETAIL_CHARS]}", artifact)
            )

    if result.returncode != 0 and not any(f.severity is Severity.ERROR for f in findings):
        detail = (result.stderr or result.stdout or "").strip()[:DETAIL_CHARS]
        findings.append(
            _finding(
                Severity.ERROR,
                f"lean exited {result.returncode}: {detail or 'no output'}",
                artifact,
            )
        )
    return findings


def elaborate(  # noqa: PLR0913 - resource limits and isolation are independent controls
    directory: Path,
    workspace: Path,
    *,
    sandbox_runner: Path | None = None,
    timeout_seconds: int = DEFAULT_TIMEOUT_SECONDS,
    memory_mb: int = DEFAULT_MEMORY_MB,
    heartbeats: int = DEFAULT_HEARTBEATS,
) -> tuple[Finding, ...]:
    if not any((workspace / name).is_file() for name in ("lakefile.lean", "lakefile.toml")):
        raise WorkspaceError(f"{workspace}: not a Lake project (no lakefile.lean or lakefile.toml)")
    if shutil.which("lake") is None:
        raise WorkspaceError("`lake` is not on PATH on this runner")

    if sandbox_runner is not None and not sandbox_runner.is_file():
        raise WorkspaceError(f"sandbox runner {sandbox_runner} does not exist")

    sandbox = [] if sandbox_runner is not None else network_sandbox()
    findings: list[Finding] = []
    if sandbox_runner is None and not sandbox:
        findings.append(
            Finding(
                CHECK_ID,
                Severity.REVIEW,
                "unprivileged user namespaces are unavailable; elaboration had network access",
            )
        )

    with tempfile.TemporaryDirectory(prefix="contrib-lean-") as scratch:
        scratch_path = Path(scratch)
        env = _environment(scratch_path)
        for source in sorted(directory.glob(f"*{LEAN_SUFFIX}")):
            if sandbox_runner is not None:
                argv = [
                    str(sandbox_runner),
                    str(workspace),
                    str(source),
                    str(timeout_seconds),
                    str(memory_mb),
                    str(heartbeats),
                ]
                cwd = None
            else:
                staged = scratch_path / source.name
                staged.write_bytes(source.read_bytes())
                argv = [
                    *sandbox,
                    "timeout",
                    "--kill-after=15",
                    str(timeout_seconds),
                    "lake",
                    "env",
                    "lean",
                    "--json",
                    f"--memory={memory_mb}",
                    f"--timeout={heartbeats}",
                    str(staged),
                ]
                cwd = workspace
            result = subprocess.run(  # noqa: S603 - argv is built from literals and paths
                argv, cwd=cwd, env=env, capture_output=True, text=True, check=False
            )
            findings.extend(_report_file(source.name, result))
    return tuple(findings)
