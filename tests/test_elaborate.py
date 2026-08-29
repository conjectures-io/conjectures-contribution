from __future__ import annotations

import subprocess
from pathlib import Path

import pytest

from conjectures_contribution import elaborate


def _lake(_name: str) -> str:
    return "/usr/bin/lake"


def _project(tmp_path: Path) -> tuple[Path, Path, Path]:
    workspace = tmp_path / "formal-conjectures"
    workspace.mkdir()
    (workspace / "lakefile.toml").write_text("name = 'test'\n", encoding="utf-8")
    contribution = tmp_path / "contribution"
    contribution.mkdir()
    source = contribution / "Proof.lean"
    source.write_text("theorem proof : True := trivial\n", encoding="utf-8")
    sandbox = tmp_path / "lean-sandbox"
    sandbox.write_text("#!/bin/sh\n", encoding="utf-8")
    return workspace, contribution, sandbox


def test_external_sandbox_is_used_without_a_network_review(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    workspace, contribution, sandbox = _project(tmp_path)
    invoked: list[list[str]] = []

    def fake_run(argv: list[str], **_kwargs: object) -> subprocess.CompletedProcess[str]:
        invoked.append(argv)
        return subprocess.CompletedProcess(argv, 0, stdout="", stderr="")

    monkeypatch.setattr("conjectures_contribution.elaborate.shutil.which", _lake)
    monkeypatch.setattr("conjectures_contribution.elaborate.subprocess.run", fake_run)

    findings = elaborate.elaborate(contribution, workspace, sandbox_runner=sandbox)

    assert findings == ()
    assert invoked == [
        [str(sandbox), str(workspace), str(contribution / "Proof.lean"), "900", "8192", "400000"]
    ]


def test_a_missing_external_sandbox_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    workspace, contribution, _sandbox = _project(tmp_path)
    monkeypatch.setattr("conjectures_contribution.elaborate.shutil.which", _lake)

    with pytest.raises(elaborate.WorkspaceError, match="does not exist"):
        elaborate.elaborate(contribution, workspace, sandbox_runner=tmp_path / "missing-sandbox")
