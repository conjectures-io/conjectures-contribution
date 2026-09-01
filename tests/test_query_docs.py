from __future__ import annotations

import re
import shlex
from pathlib import Path

import pytest
from typer.testing import CliRunner

from conjectures_contribution.cli import config
from conjectures_contribution.cli.main import app
from conjectures_contribution.cli.repo import ROOT_ENV
from conjectures_contribution.query import GRAINS

from .conftest import AUTHOR_A, QueryRepo, make_query_repo, plain

runner = CliRunner()
ROOT = Path(__file__).resolve().parent.parent
# The documents that describe the surface as built. `notes/` are design records and
# deliberately spell out rungs that do not exist yet.
REFERENCE = ROOT / "docs" / "querying.md"
DOCUMENTED = (*sorted((ROOT / "docs").glob("*.md")), ROOT / "README.md")
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


def _documented_columns() -> dict[str, list[str]]:
    documented: dict[str, list[str]] = {}
    grain: str | None = None
    for line in REFERENCE.read_text(encoding="utf-8").splitlines():
        heading = re.fullmatch(r"### `(\w+)`", line)
        if heading is not None:
            grain = str(heading.group(1))
            documented[grain] = []
        elif grain is not None:
            cell = re.match(r"\| `(\w+)` \|", line)
            if cell is not None:
                documented[grain].append(cell.group(1))
    return documented


# The column tables are the part of the reference that goes stale first, so a column added
# or renamed in the code fails here rather than quietly disagreeing with the documentation.
def test_the_reference_documents_exactly_the_columns_that_exist() -> None:
    documented = _documented_columns()
    assert set(documented) == set(GRAINS)
    for name, grain in GRAINS.items():
        assert documented[name] == list(grain.names()), name


# A renamed flag fails here rather than misleading a reader, which is the same trick
# tests/test_install.py plays on install.sh.
@pytest.mark.parametrize(("document", "command"), _commands(), ids=lambda v: str(v)[:60])
@pytest.mark.usefixtures("here")
def test_every_documented_invocation_still_runs(document: str, command: str) -> None:
    result = runner.invoke(app, shlex.split(command)[1:])
    assert result.exit_code in {0, 3}, f"{document}: {command}\n{plain(result.output)}"
