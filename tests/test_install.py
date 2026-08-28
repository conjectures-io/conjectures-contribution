from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest
from typer.testing import CliRunner

from conjectures_contribution.cli.main import app

INSTALLER = Path(__file__).resolve().parent.parent / "install.sh"
runner = CliRunner()


def test_the_installer_is_executable() -> None:
    assert INSTALLER.is_file()
    assert INSTALLER.stat().st_mode & 0o111


def test_the_installer_parses() -> None:
    shell = shutil.which("sh")
    assert shell is not None
    subprocess.run([shell, "-n", str(INSTALLER)], check=True)  # noqa: S603


# The installer drives the CLI by name, so a rename has to fail here rather than halfway
# through somebody's first install.
@pytest.mark.parametrize(
    ("fragment", "argv"),
    [
        ("repo pin", ["repo", "pin", "--help"]),
        ("config show", ["config", "show", "--help"]),
        ("--version", ["--version"]),
    ],
)
def test_the_installer_only_calls_commands_that_exist(fragment: str, argv: list[str]) -> None:
    assert fragment in INSTALLER.read_text(encoding="utf-8")
    assert runner.invoke(app, argv).exit_code == 0


def test_the_installer_installs_completion() -> None:
    assert "--install-completion" in INSTALLER.read_text(encoding="utf-8")
    assert "--install-completion" in runner.invoke(app, ["--help"]).output


# The marker every command resolves against lives in a submodule, so an install that skips it
# leaves a `contrib` that cannot find its pool.
def test_the_installer_checks_out_the_submodule() -> None:
    body = INSTALLER.read_text(encoding="utf-8")
    assert "conjectures/allowlist.json" in body
    assert "submodule update --init" in body
