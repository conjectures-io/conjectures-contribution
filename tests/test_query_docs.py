from __future__ import annotations

import re
import shlex
from pathlib import Path

import pytest
from typer.testing import CliRunner

from conjectures_contribution.cli import config
from conjectures_contribution.cli.main import app
from conjectures_contribution.cli.repo import ROOT_ENV

from .conftest import AUTHOR_A, QueryRepo, make_query_repo, plain

runner = CliRunner()
ROOT = Path(__file__).resolve().parent.parent
# The two documents that describe the surface as built. `notes/` are design records and
# deliberately spell out rungs that do not exist yet.
DOCUMENTED = (
    ROOT / ".claude" / "skills" / "contribution-corpus" / "SKILL.md",
    ROOT / "README.md",
)
_INVOCATION = re.compile(r"`?(contrib (?:ls|doctor)\b[^`\n]*)")


def _commands() -> list[tuple[str, str]]:
    found: list[tuple[str, str]] = []
    for document in DOCUMENTED:
        for line in document.read_text(encoding="utf-8").splitlines():
            match = _INVOCATION.search(line)
            if match is None:
                continue
            # Documented pipes and trailing prose are not part of the invocation.
            command = match.group(1).split("|")[0].split("#")[0].strip().rstrip("`")
            if any(placeholder in command for placeholder in "[<"):
                continue
            found.append((document.name, command))
    return found


@pytest.fixture(autouse=True)
def _isolated(  # pyright: ignore[reportUnusedFunction]
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.delenv(ROOT_ENV, raising=False)
    monkeypatch.setenv(config.CONFIG_FILE_ENV, str(tmp_path / "home" / "contribution.toml"))


@pytest.fixture
def here(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> QueryRepo:
    directory = tmp_path / "repo"
    directory.mkdir()
    found = make_query_repo(directory)
    monkeypatch.chdir(found.root)
    config.write(config.ConfigKey.AUTHOR_KEY, AUTHOR_A)
    return found


def test_the_documents_carry_invocations_at_all() -> None:
    assert len(_commands()) > 15


# A renamed flag fails here rather than misleading a reader, which is the same trick
# tests/test_install.py plays on install.sh.
@pytest.mark.parametrize(("document", "command"), _commands(), ids=lambda v: str(v)[:60])
@pytest.mark.usefixtures("here")
def test_every_documented_invocation_still_runs(document: str, command: str) -> None:
    result = runner.invoke(app, shlex.split(command)[1:])
    assert result.exit_code in {0, 3}, f"{document}: {command}\n{plain(result.output)}"
